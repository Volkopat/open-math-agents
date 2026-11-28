import OMAStatements.S_wp_eilenberg_ganea_conjecture
import Mathlib
/- Port of openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
namespace OrbitSlice
open MeasureTheory MeasureTheory.Measure Set Filter Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
 [MeasurableSpace E] [BorelSpace E]
/-- A chart of bad parameters is negligible if every parameter in its image has
  a representative in a proper real hyperplane of the chart. -/
theorem Gv (μ:Measure E) [IsAddHaarMeasure μ] (P:Submodule ℝ E)
  (hP:P ≠ ⊤) (D:Set E) (f:E → E) (hf:DifferentiableOn ℝ f D)
  (rep:∀ x ∈ D,∃ y ∈ D,y ∈ P ∧ f y = f x):μ (f '' D) = 0:=by
 have hs:f '' D ⊆ f '' (D ∩ (P:Set E)):=by
  rintro _ ⟨x,hx,rfl⟩
  obtain ⟨y,hy,hp,he⟩:=rep x hx
  exact ⟨y,⟨hy,hp⟩,he⟩
 apply measure_mono_null hs
 apply addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero μ (hf.mono inter_subset_left)
 exact measure_mono_null inter_subset_right (addHaar_submodule μ P hP)

/-- Explicit phase slice at any nonzero complex coordinate. -/
theorem Fh (z:ℂ) (hz:z ≠ 0):∃ c:ℂ,‖c‖ = 1 ∧ (c*z).im = 0:=by
 refine ⟨(‖z‖ : ℂ) / z,?_,?_⟩
 ·rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),div_self (norm_ne_zero_iff.mpr hz)]
 ·simp [div_mul_cancel₀ _ hz]
abbrev V (m:ℕ):=Fin m → ℂ
abbrev X (m:ℕ):=V m × V m
abbrev Params (m:ℕ):=Fin m → X m
/-- Parameter charts use the omitted parameter slot to store the candidate root. -/
theorem Gw {m:ℕ} [MeasurableSpace (Params m)] [BorelSpace (Params m)] (μ:Measure (Params m)) [IsAddHaarMeasure μ]
    (i:Fin m) (f:Params m → Params m)
    (hf:DifferentiableOn ℝ f {p | (p i).2 i ≠ 0})
    (rot:∀ p (c:ℂ),‖c‖ = 1 →
      f (Function.update p i ((p i).1,c • (p i).2)) = f p) :
    μ (f '' {p | (p i).2 i ≠ 0}) = 0:=by
  let l:Params m →ₗ[ℝ] ℝ:={
    toFun:=fun p=>((p i).2 i).im
    map_add':=by intros; rfl
    map_smul':=by intro r p; exact Complex.smul_im r _ }
  refine Gv μ l.ker ?_ _ f hf ?_
  · intro h
    have hh:(fun _:Fin m=>((0:V m),fun _:Fin m=>Complex.I)) ∈ l.ker:=by rw [h]; trivial
    change Complex.I.im = 0 at hh
    norm_num at hh
  · intro p hp
    obtain ⟨c,hc,hz⟩:=Fh _ hp
    refine ⟨Function.update p i ((p i).1,c • (p i).2),?_,?_,rot p c hc⟩
    · have hcn:c ≠ 0:=by intro h; simp [h] at hc
      simpa using mul_ne_zero hcn hp
    · change ((Function.update p i ((p i).1,c • (p i).2) i).2 i).im = 0
      simpa using hz
end OrbitSlice
section
namespace OAI
noncomputable section
open Classical Set
namespace EilenbergGanea
def seedWord:Bool -> List (Bool × Bool)
  | false=>[(false,true),(false,true),(true,false),(true,false),
      (true,false),(true,false),(true,false)]
  | true=>[(false,true),(false,true),(true,true),(false,false),
      (true,true),(false,false),(true,true),(false,false)]
def kF (r:Bool):ℕ:=3 * (seedWord r).length
abbrev oP:=Option (Bool × Fin 2)
abbrev SeedVertex:=oP ⊕ Bool
abbrev nF:=Bool × Fin 3
abbrev jN:=(r:Bool) × Fin (kF r)
abbrev SeedEdge:=nF ⊕ jN
abbrev SeedCell:=SeedVertex ⊕ (SeedEdge ⊕ jN)
def gX (e:nF):oP:=
 ![none,some (e.1,0),some (e.1,1)] e.2
def lW (e:nF):oP:=
 ![some (e.1,0),some (e.1,1),none] e.2
def jW (s:jN):Bool × Bool:=
 (seedWord s.1).get ⟨s.2.val / 3,by
  have h:=s.2.isLt
  dsimp [kF] at h
  omega⟩
def dV (s:jN):nF:=
 ((jW s).1,if (jW s).2 then
  ⟨s.2.val % 3,Nat.mod_lt _ (by decide)⟩ else
  ⟨2 - s.2.val % 3,by omega⟩)
def lC (s:jN):oP:=
 if (jW s).2 then gX (dV s)
 else lW (dV s)
def nI (s:jN):jN:=
 ⟨s.1,⟨(s.2.val + 1) % kF s.1,
  Nat.mod_lt _ (by have:=s.2.isLt; omega)⟩⟩
def dS:SeedEdge -> Finset SeedVertex
 | .inl e=>{.inl (gX e),.inl (lW e)}
 | .inr s=>{.inr s.1,.inl (lC s)}
def lD (s:jN):Finset SeedEdge:=
 {.inl (dV s),.inr s,.inr (nI s)}
def xP (s:jN):Finset SeedVertex:=
 (lD s).biUnion dS
def dD:SeedCell -> SeedCell -> Prop
 | .inl v,.inr (.inl e)=>v ∈ dS e
 | .inl v,.inr (.inr s)=>v ∈ xP s
 | .inr (.inl e),.inr (.inr s)=>e ∈ lD s
 | _,_=>False
def seedGraph:SimpleGraph SeedCell where
 Adj a b:=dD a b \/ dD b a
 symm:=⟨fun _ _ h=>h.elim Or.inr Or.inl⟩
 loopless:=⟨by
  intro a
  rcases a with a | a
  ·simp [dD]
  ·rcases a with a | a <;> simp [dD]⟩
def seedBase:SeedCell:=.inl (.inl none)
theorem seed_vertex_edge_adj {v:SeedVertex} {e:SeedEdge} (h:v ∈ dS e) :
  seedGraph.Adj (.inl v) (.inr (.inl e)):=Or.inl h
theorem seed_edge_sector_adj {e:SeedEdge} {s:jN} (h:e ∈ lD s) :
  seedGraph.Adj (.inr (.inl e)) (.inr (.inr s)):=Or.inl h
theorem qC (v:oP) :
  seedGraph.Reachable seedBase (.inl (.inl v)):=by
 rcases v with _ | ⟨b,i⟩
 ·exact .refl _
 ·fin_cases i
  ·have h₁:seedGraph.Adj seedBase (.inr (.inl (.inl (b,0)))):=by
    apply seed_vertex_edge_adj
    simp [dS,gX,lW]
   have h₂:seedGraph.Adj (.inl (.inl (some (b,0))))
     (.inr (.inl (.inl (b,0)))):=by
    apply seed_vertex_edge_adj
    simp [dS,gX,lW]
   exact h₁.reachable.trans h₂.reachable.symm
  ·have h₁:seedGraph.Adj seedBase (.inr (.inl (.inl (b,2)))):=by
    apply seed_vertex_edge_adj
    simp [dS,gX,lW]
   have h₂:seedGraph.Adj (.inl (.inl (some (b,1))))
     (.inr (.inl (.inl (b,2)))):=by
    apply seed_vertex_edge_adj
    simp [dS,gX,lW]
   exact h₁.reachable.trans h₂.reachable.symm
def BU (r:Bool):jN:=
 ⟨r,⟨0,by cases r <;> decide⟩⟩
theorem seed_vertex_reachable (v:SeedVertex) :
  seedGraph.Reachable seedBase (.inl v):=by
 rcases v with v | r
 ·exact qC v
 ·let s:=BU r
  have h₁:seedGraph.Adj (.inl (.inl (lC s))) (.inr (.inl (.inr s))):=by
   apply seed_vertex_edge_adj
   simp [dS]
  have h₂:seedGraph.Adj (.inl (.inr r)) (.inr (.inl (.inr s))):=by
   apply seed_vertex_edge_adj
   simp [dS,s,BU]
  exact ((qC (lC s)).trans h₁.reachable).trans h₂.reachable.symm
theorem seed_edge_reachable (e:SeedEdge) :
  seedGraph.Reachable seedBase (.inr (.inl e)):=by
 rcases e with e | s
 ·apply (seed_vertex_reachable (.inl (gX e))).trans
  apply SimpleGraph.Adj.reachable
  apply seed_vertex_edge_adj
  simp [dS]
 ·apply (seed_vertex_reachable (.inr s.1)).trans
  apply SimpleGraph.Adj.reachable
  apply seed_vertex_edge_adj
  simp [dS]
theorem seed_cell_reachable (x:SeedCell):seedGraph.Reachable seedBase x:=by
 rcases x with v | e
 ·exact seed_vertex_reachable v
 ·rcases e with e | s
  ·exact seed_edge_reachable e
  ·apply (seed_edge_reachable (.inl (dV s))).trans
   apply SimpleGraph.Adj.reachable
   apply seed_edge_sector_adj
   simp [lD]
theorem seed_connected:seedGraph.Connected:=by
  exact { preconnected:=fun v w=>
    (seed_cell_reachable v).symm.trans (seed_cell_reachable w),nonempty:=⟨seedBase⟩ }
end EilenbergGanea
end
noncomputable section
open Classical Set
namespace SimplicialChains
variable {V:Type*}
abbrev Chains (V:Type*):=List V →₀ ℤ
def front (v:V):Chains V →ₗ[ℤ] Chains V:=Finsupp.lmapDomain ℤ ℤ (List.cons v)
@[simp] theorem jO (v:V) (w:List V) (n:ℤ) :
  front v (Finsupp.single w n)=Finsupp.single (v::w) n:=by simp [front]
def cP:List V -> Chains V
 | []=>0
 | v::w=>Finsupp.single w 1 - front v (cP w)
def boundary:Chains V →ₗ[ℤ] Chains V:=Finsupp.linearCombination ℤ cP
@[simp] theorem gI (w:List V) (n:ℤ) :
  boundary (Finsupp.single w n)=n • cP w:=by simp [boundary]
@[simp] theorem nJ:cP ([]:List V)=0:=rfl
@[simp] theorem dK (v:V) (w:List V) :
  cP (v::w)=Finsupp.single w 1 - front v (cP w):=rfl
def yP {I:Type*} [Fintype I] (f:I -> List V):(I -> ℤ) →ₗ[ℤ] Chains V:=
 (Pi.basisFun ℤ I).constr ℤ (fun i=>Finsupp.single (f i) 1)
@[simp] theorem JM {I:Type*} [Fintype I] [DecidableEq I] (f:I -> List V) (i:I) :
  yP f (Pi.single i 1)=Finsupp.single (f i) 1:=by
 have hb:(Pi.basisFun ℤ I) i=Pi.single i 1:=by
  funext j
  simp [Pi.basisFun_apply,Pi.single_apply]
 rw [<- hb]
 exact (Pi.basisFun ℤ I).constr_basis ℤ _ i
variable [LinearOrder V] (L:SimpleGraph V)
def Valid (w:List V):Prop:=w.Pairwise (· < ·) /\ w.Pairwise L.Adj
def chains (k:ℕ):Submodule ℤ (Chains V):=
 Finsupp.supported ℤ ℤ {w | Valid L w /\ w.length=k}
structure Contraction where
 homotopy:Chains V →ₗ[ℤ] Chains V
 degree:∀ k c,c ∈ chains L k -> homotopy c ∈ chains L (k+1)
 identity:∀ w,Valid L w ->
  boundary (homotopy (Finsupp.single w 1)) + homotopy (cP w) =
   Finsupp.single w 1
variable {L}
theorem zP {w u:List V} (hw:Valid L w) (hu:u.Sublist w):Valid L u:=
 ⟨hw.1.sublist hu,hw.2.sublist hu⟩
structure TwoDimensionalIndices (E T:Type*) where
 edge:E -> V × V
 triangle:T -> V × V × V
 face:T -> E × E × E
 edgeIndex:V -> V -> E
 triangleIndex:V -> V -> V -> T
 edge_valid:∀ e,Valid L [(edge e).1,(edge e).2]
 triangle_valid:∀ t,Valid L [(triangle t).1,(triangle t).2.1,(triangle t).2.2]
 edge_inverse:∀ e,edgeIndex (edge e).1 (edge e).2=e
 edge_complete:∀ a b,Valid L [a,b] -> edge (edgeIndex a b)=(a,b)
 triangle_complete:∀ a b c,Valid L [a,b,c] -> triangle (triangleIndex a b c)=(a,b,c)
 face_edge:∀ t,
  edge (face t).1=((triangle t).2.1,(triangle t).2.2) /\
  edge (face t).2.1=((triangle t).1,(triangle t).2.2) /\
  edge (face t).2.2=((triangle t).1,(triangle t).2.1)
 length_le:∀ w,Valid L w -> w.length <= 3
namespace TwoDimensionalIndices
variable {E T:Type*} [Fintype V] [Fintype E] [Fintype T]
variable (D:TwoDimensionalIndices (L:=L) E T)
def eList (e:E):List V:=[(D.edge e).1,(D.edge e).2]
def Nd (t:T):List V:=[(D.triangle t).1,(D.triangle t).2.1,(D.triangle t).2.2]
variable (root:V) (h₀:(V -> ℤ) →ₗ[ℤ] (E -> ℤ))
  (h₁:(E -> ℤ) →ₗ[ℤ] (T -> ℤ))
def Ej:List V -> Chains V
 | []=>Finsupp.single [root] 1
 | [v]=>yP D.eList (h₀ (Pi.single v 1))
 | [a,b]=>yP D.Nd (h₁ (Pi.single (D.edgeIndex a b) 1))
 | _=>0
def fill:Chains V →ₗ[ℤ] Chains V:=Finsupp.linearCombination ℤ (D.Ej root h₀ h₁)
omit [Fintype V] in
@[simp] theorem Nc (w:List V) (n:ℤ) :
  D.fill root h₀ h₁ (Finsupp.single w n)=n • D.Ej root h₀ h₁ w:=by simp [fill]
end TwoDimensionalIndices
end SimplicialChains
namespace SimplicialChains
variable {V W:Type*}
def reindex (f:V -> W):Chains V →ₗ[ℤ] Chains W:=
 Finsupp.lmapDomain ℤ ℤ (List.map f)
@[simp] theorem rE (f:V -> W) (w:List V) (n:ℤ) :
  reindex f (Finsupp.single w n)=Finsupp.single (w.map f) n:=by simp [reindex]
@[simp] theorem DZ (f:V -> W) (v:V) (c:Chains V) :
  reindex f (front v c)=front (f v) (reindex f c):=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]
 | single w n=>simp
theorem qI (f:V -> W) (w:List V) :
  reindex f (cP w)=cP (w.map f):=by
 induction w with
 | nil=>simp
 | cons v w ih=>simp only [dK,map_sub,rE,DZ,ih,List.map_cons]
theorem Cn (f:V -> W) (c:Chains V) :
  reindex f (boundary c)=boundary (reindex f c):=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]
 | single w n=>simp [qI]
@[simp] theorem Kp (e:V ≃ W) (c:Chains V) :
  reindex e.symm (reindex e c)=c:=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]
 | single w n=>simp
variable [LinearOrder V] [LinearOrder W] {L:SimpleGraph V} {M:SimpleGraph W}
theorem xQ (f:V -> W) (hf:∀ w,Valid L w -> Valid M (w.map f))
  {k:ℕ} {c:Chains V} (hc:c ∈ chains L k):reindex f c ∈ chains M k:=by
 rw [chains,Finsupp.supported_eq_span_single] at hc
 apply Submodule.span_induction (p:=fun c _=>reindex f c ∈ chains M k) _ _ _ _ hc
 ·rintro _ ⟨w,⟨hw,hl⟩,rfl⟩
  rw [rE]
  exact Finsupp.single_mem_supported ℤ 1 ⟨hf w hw,by simpa using hl⟩
 ·simp
 ·intro c d _ _ hc hd; simpa only [map_add] using (chains M k).add_mem hc hd
 ·intro n c _ hc; simpa only [map_smul] using (chains M k).smul_mem n hc
def Contraction.reindex (K:Contraction L) (e:V ≃ W)
    (hf:∀ w,Valid L w -> Valid M (w.map e))
    (hb:∀ w,Valid M w -> Valid L (w.map e.symm)):Contraction M where
  homotopy:=(SimplicialChains.reindex e).comp (K.homotopy.comp (SimplicialChains.reindex e.symm))
  degree:=by
    intro k c hc
    exact xQ e hf (K.degree k _ (xQ e.symm hb hc))
  identity:=by
    intro w hw
    have hh:=congrArg (SimplicialChains.reindex e) (K.identity (w.map e.symm) (hb w hw))
    simp only [map_add,Cn,<- qI] at hh
    simpa only [LinearMap.comp_apply,rE,List.map_map,Equiv.apply_symm_apply,
      Function.comp_def,List.map_id_fun',id_eq] using hh
end SimplicialChains
end
noncomputable section
open Classical Set
namespace EilenbergGanea
namespace SeedEncoding
def finite (n:ℕ):Fin 103:=⟨n % 103,Nat.mod_lt _ (by decide)⟩
def roseAt:ℕ -> oP
 | 0=>none
 | 1=>some (false,0)
 | 2=>some (false,1)
 | 3=>some (true,0)
 | _=>some (true,1)
def sectorAt (n:ℕ):jN:=
 if n < 21 then ⟨false,⟨n % 21,by change n % 21 < 21; omega⟩⟩
 else ⟨true,⟨(n-21) % 24,by change (n-21) % 24 < 24; omega⟩⟩
def cellAt (i:Fin 103):SeedCell:=
 if i.val < 5 then .inl (.inl (roseAt i.val))
 else if i.val < 7 then .inl (.inr (decide (i.val=6)))
 else if i.val < 13 then .inr (.inl (.inl (decide (10 <= i.val),⟨(i.val-7)%3,by omega⟩)))
 else if i.val < 58 then .inr (.inl (.inr (sectorAt (i.val-13))))
 else .inr (.inr (sectorAt (i.val-58)))
def sectorCode (s:jN):ℕ:=(if s.1 then 21 else 0) + s.2.val
def cellCode:SeedCell -> Fin 103
 | .inl (.inl none)=>finite 0
 | .inl (.inl (some (q,j)))=>finite (1 + (if q then 2 else 0) + j.val)
 | .inl (.inr r)=>finite (5 + if r then 1 else 0)
 | .inr (.inl (.inl (q,j)))=>finite (7 + (if q then 3 else 0) + j.val)
 | .inr (.inl (.inr s))=>finite (13 + sectorCode s)
 | .inr (.inr s)=>finite (58 + sectorCode s)
theorem cellAt_code (c:SeedCell):cellAt (cellCode c)=c:=by
 rcases c with (v|e)
 ·rcases v with (v|r)
  ·rcases v with _ | ⟨q,j⟩
   ·decide +kernel
   ·cases q <;> fin_cases j <;> decide +kernel
  ·cases r <;> decide +kernel
 ·rcases e with (e|s)
  ·rcases e with (⟨q,j⟩|⟨r,i⟩)
   ·cases q <;> fin_cases j <;> decide +kernel
   ·cases r <;> fin_cases i <;> decide +kernel
  ·rcases s with ⟨r,i⟩
   cases r <;> fin_cases i <;> decide +kernel
theorem code_cellAt:∀ i:Fin 103,cellCode (cellAt i)=i:=by decide +kernel
def cellEquiv:SeedCell ≃ Fin 103 where
 toFun:=cellCode
 invFun:=cellAt
 left_inv:=cellAt_code
 right_inv:=code_cellAt
instance properFaceDecidable:DecidableRel dD:=by
 intro a b
 unfold dD
 split <;> infer_instance
instance seedAdjDecidable:DecidableRel seedGraph.Adj:=
 fun a b=>inferInstanceAs (Decidable (dD a b \/ dD b a))
def adjCodes:List ℕ:=[7243717715589717591194788771456,7726619075706194405914338017664,3863334018612617729895957824256,482913190295244515963480050688,965825603447607950602534918144,604462621576955615502336,10141204197363213635018010132480,5151073943635249663071907479555,2575545132070798340360931115014,1287788886541746187830420307973,160971236130163140008121204745,321941954165072225809775722520,643883649282517424516318101521,302231743134033445388321,864691128455135266,1729382256910270500,3458764513820540961,6917529027641081890,13835058055282163748,27670116110564327457,55340232221128654896,110680464442257309736,221360928884514619425,442721857769029238832,885443715538058477608,1770887431076116955169,3541774862152233910320,7083549724304467820584,14167099448608935641121,28334198897217871282224,56668397794435742564392,113336795588871485128737,226673591177742970257456,453347182355485940514856,5070603005375827413301400174657,1813388729421943762059330,3626777458843887524118596,7253554917687775048237121,14507109835375550096474178,29014219670751100192948292,58028439341502200385896513,116056878683004400771792968,232113757366008801543585872,464227514732017603087171649,928455029464035206174343236,1856910058928070412348686402,3713820117856140824697372737,7427640235712281649394745416,14855280471424563298789490768,29710560942849126597578981441,59421121885698253195157962820,118842243771396506390315925570,237684487542793012780631851073,475368975085586025561263702088,950737950171172051122527404112,1901475900342344102245054808129,3802951800684688204490109616196,7605903601369376408980219232322,24739,49446,98853,196771,393510,786981,1577009,3147832,6292521,12587057,25167928,50332713,100667441,201328696,402654249,805310513,1610614840,3221226537,6442455089,12884903992,8589943849,51539607747,103079215430,206158430789,412316860611,824633721158,1649267442245,3298534884425,6597069768792,13194139537489,26388279067205,52776558133574,105553116266691,211106232534089,422212465068120,844424930136145,1688849860264517,3377699720528198,6755399441055939,13510798882112585,27021597764225112,54043195528450129,108086391056892485,216172782113784134,144115205255725251]
def indexedAdj (a b:Fin 103):Prop:=((adjCodes.getD a.val 0 >>> b.val) % 2)=1
instance:DecidableRel indexedAdj:=fun a b=>inferInstanceAs (Decidable (((adjCodes.getD a.val 0 >>> b.val) % 2)=1))
theorem adjacency_certificate:∀ a b:Fin 103,
  seedGraph.Adj (cellAt a) (cellAt b) ↔ indexedAdj a b:=by decide +kernel
end SeedEncoding
end EilenbergGanea
namespace EilenbergGanea.SeedChainCertificate
def rankIndex (a:Fin 103):Fin 3:=if a.val < 7 then 0 else if a.val < 58 then 1 else 2
 theorem sorted_adj_rank:∀ a b:Fin 103,a < b -> SeedEncoding.indexedAdj a b ->
    rankIndex a < rankIndex b:=by decide +kernel
open SimplicialChains
def graph:SimpleGraph (Fin 103):=seedGraph.comap SeedEncoding.cellAt
@[simp] theorem graph_adj (a b:Fin 103):graph.Adj a b ↔ SeedEncoding.indexedAdj a b:=
  SeedEncoding.adjacency_certificate a b
 theorem valid_length_le (w:List (Fin 103)) (hw:Valid graph w):w.length <= 3:=by
  have hp:w.Pairwise (fun a b=>rankIndex a < rankIndex b):=by
    have hh:=hw.1.and hw.2
    exact hh.imp (fun {a b} h=>sorted_adj_rank a b h.1 ((graph_adj a b).mp h.2))
  have hn:(w.map rankIndex).Nodup:=by
    apply List.nodup_iff_pairwise_ne.mpr
    rw [List.pairwise_map]
    exact hp.imp (fun {_ _} h=>ne_of_lt h)
  have he:=hn.length_le_card
  simpa using he
end EilenbergGanea.SeedChainCertificate
end
noncomputable section
open Classical Set
open Classical
namespace CubicalChains
variable {G A:Type*} [Group G]
abbrev Chains (G A:Type*):=(G × List A) →₀ ℤ
def front (x:A):Chains G A →ₗ[ℤ] Chains G A:=
 Finsupp.lmapDomain ℤ ℤ (fun p=>(p.1,x :: p.2))
def shift (v:A -> G) (x:A):Chains G A →ₗ[ℤ] Chains G A:=
 Finsupp.lmapDomain ℤ ℤ (fun p=>(p.1 * v x,p.2))
omit [Group G] in
@[simp] theorem jO (x:A) (g:G) (w:List A) (n:ℤ) :
  front x (Finsupp.single (g,w) n)=Finsupp.single (g,x::w) n:=by
 simp [front]
@[simp] theorem Ja (v:A -> G) (x:A) (g:G) (w:List A) (n:ℤ) :
  shift v x (Finsupp.single (g,w) n)=Finsupp.single (g*v x,w) n:=by
 simp [shift]
def cP (v:A -> G) (g:G):List A -> Chains G A
 | []=>0
 | x :: w=>Finsupp.single (g*v x,w) 1 - Finsupp.single (g,w) 1 -
   front x (cP v g w)
def boundary (v:A -> G):Chains G A →ₗ[ℤ] Chains G A:=
 Finsupp.linearCombination ℤ (fun p=>cP v p.1 p.2)
@[simp] theorem gI (v:A -> G) (g:G) (w:List A) (n:ℤ) :
  boundary v (Finsupp.single (g,w) n)=n • cP v g w:=by
 simp [boundary]
@[simp] theorem nJ (v:A -> G) (g:G):cP v g []=0:=rfl
@[simp] theorem dK (v:A -> G) (g:G) (x:A) (w:List A) :
  cP v g (x :: w)=Finsupp.single (g*v x,w) 1 - Finsupp.single (g,w) 1 -
   front x (cP v g w):=rfl
theorem rF (v:A -> G) (x:A) (c:Chains G A) :
  boundary v (front x c)=shift v x c - c - front x (boundary v c):=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]; abel
 | single p n=>
   rcases p with ⟨g,w⟩
   simp only [jO,gI,dK,Ja,map_smul]
   simp only [smul_sub,Finsupp.smul_single,smul_eq_mul,mul_one]
theorem Ru (v:A -> G) (x y:A) (c:Chains G A) :
  shift v x (front y c)=front y (shift v x c):=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]
 | single p n=>rcases p with ⟨g,w⟩; simp
theorem Nv (v:A -> G) (x:A) (g:G) (w:List A)
    (hw:∀ y ∈ w,Commute (v x) (v y)) :
    cP v (g * v x) w=shift v x (cP v g w):=by
  induction w with
  | nil=>simp
  | cons y w ih=>
      rw [dK,dK,map_sub,map_sub,Ja,Ja,
        Ru,ih (fun z hz=>hw z (by simp [hz]))]
      rw [mul_assoc,(hw y (by simp)).eq,<- mul_assoc]
theorem qE (v:A -> G) (g:G) (w:List A)
  (hw:w.Pairwise (fun x y=>Commute (v x) (v y))) :
  boundary v (cP v g w)=0:=by
 induction w generalizing g with
 | nil=>simp
 | cons x w ih=>
   obtain ⟨hx,hw⟩:=List.pairwise_cons.mp hw
   simp only [dK,map_sub,gI,one_smul,rF]
   rw [ih _ hw,map_zero,Nv v x g w hx]
   abel
def kP (g:G):List A -> Chains G A
 | []=>0
 | x :: w=>-Finsupp.single (g,w) 1 - front x (kP g w)
def upper:Chains G A →ₗ[ℤ] Chains G A:=
 Finsupp.linearCombination ℤ (fun p=>kP p.1 p.2)
omit [Group G] in
@[simp] theorem Rw (g:G) (w:List A) (n:ℤ) :
  upper (Finsupp.single (g,w) n)=n • kP g w:=by simp [upper]
omit [Group G] in
@[simp] theorem du8 (g:G):kP g ([]:List A)=0:=rfl
omit [Group G] in
@[simp] theorem z2 (g:G) (x:A) (w:List A) :
  kP g (x::w)=-Finsupp.single (g,w) 1 - front x (kP g w):=rfl
omit [Group G] in
 theorem d8 {I J:Type*} (f:(I →₀ ℤ) →ₗ[ℤ] (J →₀ ℤ))
    (P:Set I) (Q:Set J)
    (h:∀ i ∈ P,f (Finsupp.single i 1) ∈ Finsupp.supported ℤ ℤ Q)
    {c:I →₀ ℤ} (hc:c ∈ Finsupp.supported ℤ ℤ P) :
    f c ∈ Finsupp.supported ℤ ℤ Q:=by
  rw [Finsupp.supported_eq_span_single] at hc
  change c ∈ (Finsupp.supported ℤ ℤ Q).comap f
  apply Submodule.span_le.mpr _ hc
  rintro _ ⟨i,hi,rfl⟩; exact h i hi
omit [Group G] in
 theorem m8 (g:G) (w:List A) :
    kP g w ∈ Finsupp.supported ℤ ℤ
      {p:G × List A | p.1=g /\ p.2.Sublist w /\ p.2.length + 1=w.length}:=by
  induction w with
  | nil=>simp
  | cons x w ih=>
      rw [z2]
      apply Submodule.sub_mem
      · apply Submodule.neg_mem
        exact Finsupp.single_mem_supported ℤ 1 ⟨rfl,List.sublist_cons_self _ _,rfl⟩
      · apply d8 (front x) _ _ _ ih
        rintro ⟨g',w'⟩ ⟨rfl,hs,hl⟩
        rw [jO]
        exact Finsupp.single_mem_supported ℤ 1 ⟨rfl,hs.cons_cons x,by simp; omega⟩
def Removed (x:A) (w u:List A):Prop:=
 ∃ p q,w=p ++ x :: q /\ u=p ++ q
omit [Group G] in
 theorem Removed.mem {x:A} {w u:List A} (h:Removed x w u):x ∈ w:=by
  obtain ⟨p,q,rfl,rfl⟩:=h
  simp
omit [Group G] in
 theorem Removed.sublist {x:A} {w u:List A} (h:Removed x w u):u.Sublist w:=by
  obtain ⟨p,q,rfl,rfl⟩:=h
  exact (List.sublist_cons_self x q).append_left p
omit [Group G] in
 theorem Removed.length {x:A} {w u:List A} (h:Removed x w u):u.length + 1=w.length:=by
  obtain ⟨p,q,rfl,rfl⟩:=h
  simp; omega
omit [Group G] in
 theorem Removed.dt3 {x:A} {w u:List A} (h:Removed x w u) (hw:w.Nodup):x ∉ u:=by
  obtain ⟨p,q,rfl,rfl⟩:=h
  rw [List.mem_append,not_or]
  refine ⟨?_,(List.nodup_cons.mp (List.nodup_append.mp hw).2.1).1⟩
  intro hx
  exact (List.nodup_append.mp hw).2.2 x hx x (by simp) rfl
omit [Group G] in
 theorem Removed.cons {x y:A} {w u:List A} (h:Removed x w u):Removed x (y::w) (y::u):=by
  obtain ⟨p,q,rfl,rfl⟩:=h
  exact ⟨y::p,q,rfl,rfl⟩
def kB (v:A -> G) (g:G) (w:List A):=cP v g w - kP g w
def lower (v:A -> G):Chains G A →ₗ[ℤ] Chains G A:=boundary v - upper
@[simp] theorem co2 (v:A -> G) (g:G) (w:List A) (n:ℤ) :
  lower v (Finsupp.single (g,w) n)=n • kB v g w:=by
 simp [lower,kB,smul_sub]
@[simp] theorem du2 (v:A -> G) (g:G):kB v g []=0:=by simp [kB]
@[simp] theorem Dd (v:A -> G) (g:G) (x:A) (w:List A) :
    kB v g (x::w)=Finsupp.single (g*v x,w) 1 - front x (kB v g w):=by
  simp only [kB,dK,z2,map_sub]
  abel
 theorem Ry (v:A -> G) (g:G) (w:List A) :
    kB v g w ∈ Finsupp.supported ℤ ℤ
      {p:G × List A | ∃ x,Removed x w p.2 /\ p.1=g * v x}:=by
  induction w with
  | nil=>simp
  | cons x w ih=>
      rw [Dd]
      apply Submodule.sub_mem
      · exact Finsupp.single_mem_supported ℤ 1 ⟨x,⟨[],w,rfl,rfl⟩,rfl⟩
      · apply d8 (front x) _ _ _ ih
        rintro ⟨g',w'⟩ ⟨y,hy,rfl⟩
        rw [jO]
        exact Finsupp.single_mem_supported ℤ 1 ⟨y,hy.cons,rfl⟩
end CubicalChains
end
noncomputable section
open Classical Set
namespace EilenbergGanea
def Nw {V:Type*} (L:SimpleGraph V):Set (FreeGroup V):=
  {w | ∃ q r,L.Adj q r /\
    w=FreeGroup.of q * FreeGroup.of r * (FreeGroup.of q)⁻¹ * (FreeGroup.of r)⁻¹}
abbrev a1 {V:Type*} (L:SimpleGraph V):=PresentedGroup (Nw L)
def height {V:Type*} (L:SimpleGraph V):a1 L →* Multiplicative ℤ:=
 PresentedGroup.toGroup (f:=fun _:V=>Multiplicative.ofAdd (1:ℤ)) (by
  rintro w ⟨q,r,_,rfl⟩
  simp)
section FiniteGeneration
variable {V:Type*} (L:SimpleGraph V)
abbrev a0 (v:V):a1 L:=PresentedGroup.of v
@[simp] theorem a4 (v:V) :
  height L (a0 L v)=Multiplicative.ofAdd (1:ℤ):=by
 simp [height,a0]
theorem a2 {v w:V} (h:L.Adj v w) :
  Commute (a0 L v) (a0 L w):=by
 have he:=PresentedGroup.one_of_mem (rels:=Nw L)
  (x:=FreeGroup.of v * FreeGroup.of w * (FreeGroup.of v)⁻¹ * (FreeGroup.of w)⁻¹)
  ⟨v,w,h,rfl⟩
 simp only [map_mul,map_inv] at he
 change a0 L v * a0 L w =
  a0 L w * a0 L v
 apply mul_inv_eq_one.mp
 simpa only [a0,PresentedGroup.of,mul_inv_rev,mul_assoc] using he
def Rz:Set (a1 L):=
 {x | ∃ v w,L.Adj v w /\ x=a0 L v * (a0 L w)⁻¹}
def c6:Subgroup (a1 L):=Subgroup.closure (Rz L)
theorem s9 {v w:V} (h:L.Adj v w) :
  a0 L v * (a0 L w)⁻¹ ∈ c6 L:=
 Subgroup.subset_closure ⟨v,w,h,rfl⟩
theorem Ny {v w:V} (h:L.Reachable v w) :
  a0 L v * (a0 L w)⁻¹ ∈ c6 L:=by
 obtain ⟨p⟩:=h
 induction p with
 | nil=>simp
 | @cons u v w huv p ih=>
  simpa only [mul_assoc,inv_mul_cancel_left] using
   (c6 L).mul_mem (s9 L huv) ih
theorem RA {v w:V} (h:L.Reachable v w) :
  (a0 L v)⁻¹ * a0 L w ∈ c6 L:=by
 obtain ⟨p⟩:=h
 induction p with
 | nil=>simp
 | @cons u v w huv p ih=>
  have hc:=(a2 L huv).inv_left
  have he:(a0 L u)⁻¹ * a0 L v ∈ c6 L:=by
   rw [hc.eq]
   exact s9 L huv.symm
  simpa only [mul_assoc,mul_inv_cancel_left] using (c6 L).mul_mem he ih
theorem nD {A:Type*} [Group A] (K:Subgroup A)
  {g a e:A} (hga:g * a⁻¹ ∈ K) (he:e ∈ K) (ha:Commute a e) :
  g * e * g⁻¹ ∈ K:=by
 have hm:=K.mul_mem (K.mul_mem hga he) (K.inv_mem hga)
 have hi:(g * a⁻¹) * e * (g * a⁻¹)⁻¹=g * e * g⁻¹:=by
  calc
   (g * a⁻¹) * e * (g * a⁻¹)⁻¹=g * (a⁻¹ * e * a) * g⁻¹:=by group
   _=g * e * g⁻¹:=by rw [ha.inv_left.eq]; simp [mul_assoc]
 rwa [hi] at hm
theorem RD (hconn:L.Preconnected) (v:V)
  {x:a1 L} (hx:x ∈ c6 L) :
  a0 L v * x * (a0 L v)⁻¹ ∈ c6 L:=by
 have hh:c6 L <= (c6 L).comap (MulAut.conj (a0 L v)):=by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨b,c,hbc,rfl⟩
  exact nD (c6 L)
   (Ny L (hconn v b)) (s9 L hbc)
   ((Commute.refl _).mul_right (a2 L hbc).inv_right)
 exact hh hx
theorem RG (hconn:L.Preconnected) (v:V)
  {x:a1 L} (hx:x ∈ c6 L) :
  (a0 L v)⁻¹ * x * a0 L v ∈ c6 L:=by
 have hh:c6 L <=
   (c6 L).comap (MulAut.conj ((a0 L v)⁻¹)):=by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨b,c,hbc,rfl⟩
  change (a0 L v)⁻¹ * (a0 L b * (a0 L c)⁻¹) *
   ((a0 L v)⁻¹)⁻¹ ∈ c6 L
  apply nD (c6 L) (a:=(a0 L b)⁻¹)
  ·simpa using RA L (hconn v b)
  ·exact s9 L hbc
  ·exact ((Commute.refl _).mul_right
    (a2 L hbc).inv_right).inv_left
 simpa using hh hx
theorem RH (hconn:L.Preconnected):(c6 L).Normal:=by
 apply Subgroup.normalizer_eq_top_iff.mp
 apply (Subgroup.eq_top_iff' _).mpr
 apply PresentedGroup.generated_by
 intro v
 rw [Subgroup.mem_normalizer_iff]
 intro x
 constructor
 ·exact RD L hconn v
 ·intro hx
  simpa [mul_assoc] using RG L hconn v hx
theorem qJ (hconn:L.Preconnected) (v₀:V) :
  c6 L=(height L).ker:=by
 apply le_antisymm
 ·apply (Subgroup.closure_le _).mpr
  rintro x ⟨v,w,_,rfl⟩
  simp [MonoidHom.mem_ker]
 ·let _:=RH L hconn
  let q:=QuotientGroup.mk' (c6 L)
  let z:=zpowersHom _ (q (a0 L v₀))
  have hq:q=z.comp (height L):=by
   apply PresentedGroup.ext
   intro v
   change q (a0 L v)=z (height L (a0 L v))
   rw [a4]
   change q (a0 L v)=q (a0 L v₀) ^ (1:ℤ)
   rw [zpow_one]
   apply mul_inv_eq_one.mp
   rw [<- map_inv,<- map_mul]
   exact (QuotientGroup.eq_one_iff _).mpr (Ny L (hconn v v₀))
  intro x hx
  apply (QuotientGroup.eq_one_iff x).mp
  change q x=1
  rw [hq,MonoidHom.comp_apply,(MonoidHom.mem_ker.mp hx),map_one]
end FiniteGeneration
end EilenbergGanea
end
noncomputable section
open Classical Set
namespace EilenbergGanea
universe u
def tZ (D K:Type*) [Group D] [Group K]:D →* MulAut (D -> K) where
  toFun d:=
    { toFun:=fun f x=>f (x * d)
      invFun:=fun f x=>f (x * d⁻¹)
      left_inv:=by intro f; funext x; simp [mul_assoc]
      right_inv:=by intro f; funext x; simp [mul_assoc]
      map_mul':=by intro f g; rfl }
  map_one':=by ext f x; simp
  map_mul' d e:=by ext f x; simp [mul_assoc]
section FiniteQuotientSeparation
variable {A:Type*} [Group A] [Group.ResiduallyFinite A]
theorem RI (s:Finset A) :
  ∃ H:FiniteIndexNormalSubgroup A,∀ a ∈ s,a ≠ 1 -> a ∉ H:=by
 classical
 induction s using Finset.induction_on with
 | empty=>exact ⟨.ofSubgroup ⊤,by simp⟩
 | @insert a s ha ih=>
  obtain ⟨H,hH⟩:=ih
  by_cases h1:a=1
  ·refine ⟨H,?_⟩
   intro b hb hb1
   rcases Finset.mem_insert.mp hb with rfl | hb
   ·exact (hb1 h1).elim
   ·exact hH b hb hb1
  ·obtain ⟨K,hK⟩:=Group.exists_finiteIndexNormalSubgroup_notMem a h1
   refine ⟨H ⊓ K,?_⟩
   intro b hb hb1 hm
   change b ∈ H.toSubgroup ⊓ K.toSubgroup at hm
   rcases Finset.mem_insert.mp hb with rfl | hb
   ·exact hK hm.2
   ·exact hH b hb hb1 hm.1
theorem x1 (s:Finset A) :
  ∃ H:FiniteIndexNormalSubgroup A,
   Set.InjOn (QuotientGroup.mk' H.toSubgroup) (s:Set A):=by
 classical
 obtain ⟨H,hH⟩:=RI
  ((s ×ˢ s).image (fun z=>z.1⁻¹ * z.2))
 refine ⟨H,?_⟩
 intro a ha b hb he
 by_contra hn
 apply hH (a⁻¹ * b) (Finset.mem_image.mpr ⟨(a,b),Finset.mem_product.mpr ⟨ha,hb⟩,rfl⟩)
  (fun h=>hn (eq_of_inv_mul_eq_one h))
 exact QuotientGroup.eq.mp he
end FiniteQuotientSeparation
section ArtinUniversal
variable {V W K:Type*} [Group K] (L:SimpleGraph V)
def sW (f:V -> K) (hf:∀ v w,L.Adj v w -> Commute (f v) (f w)) :
  a1 L →* K:=
 PresentedGroup.toGroup (by
  rintro _ ⟨v,w,hvw,rfl⟩
  simp only [map_mul,map_inv,FreeGroup.lift_apply_of]
  rw [(hf v w hvw).eq]
  group)
@[simp] theorem ae9 (f:V -> K)
  (hf:∀ v w,L.Adj v w -> Commute (f v) (f w)) (v:V) :
  sW L f hf (a0 L v)=f v:=by
 exact PresentedGroup.toGroup.of _
end ArtinUniversal
namespace Counter
noncomputable section
open Classical
variable {V:Type*} (L:SimpleGraph V) (w:List (V × Bool))
abbrev St:=V → ZMod (w.length+1)
def cn (t:ℕ) (c:V):ℕ:=(w.take t).countP (fun x=>x.1 = c)
def cnt (t:ℕ):St w:=fun c=>(cn w t c:ZMod _)
def Barrier:=∀ i j:Fin w.length,i < j → w[i.val].1 = w[j.val].1 → w[i.val].2 ≠ w[j.val].2 →
 ∃ k:Fin w.length,i < k ∧ k < j ∧ ¬L.Adj w[i.val].1 w[k.val].1
def Ek (a:V) (s t:St w):=∀ c,c ≠ a → ¬L.Adj a c → s c = t c
def sgn (a:V) (s:St w):Bool:=
 if h:∃ i:Fin w.length,w[i.val].1 = a ∧ Ek L w a s (cnt w i.val) then w[(Classical.choose h).val].2 else true
theorem Dh {a c:V} (s:St w) (x) (h:c = a ∨ L.Adj a c) :
  sgn L w a (Function.update s c x) = sgn L w a s:=by
 have:Ek L w a (Function.update s c x) = Ek L w a s:=by
  funext t; apply propext; unfold Ek
  refine forall_congr' fun d=>imp_congr_right fun hd=>imp_congr_right fun ha=>?_
  rw [Function.update_of_ne]; rintro rfl; rcases h with h|h; exact hd h; exact ha h
 unfold sgn; simp only [this]
@[simp] theorem Rd (a:V) (s:St w) (x):sgn L w a (Function.update s a x) = sgn L w a s:=
 Dh L w s x (Or.inl rfl)
def step (a:V):Equiv.Perm (St w) where
 toFun s:=Function.update s a (s a + if sgn L w a s then 1 else -1)
 invFun s:=Function.update s a (s a - if sgn L w a s then 1 else -1)
 left_inv s:=by simp
 right_inv s:=by simp
theorem Jb {a c:V} (h:L.Adj a c):Commute (step L w a) (step L w c):=by
  have hac:a ≠ c:=L.ne_of_adj h
  ext s d
  show step L w a (step L w c s) d = step L w c (step L w a s) d
  simp only [step,Equiv.coe_fn_mk,Dh L w s _ (Or.inr h),Dh L w s _ (Or.inr h.symm),
    Function.update_of_ne hac,Function.update_of_ne hac.symm,Function.update_apply]
  split_ifs <;> simp_all
theorem strong (H:Barrier L w) (d:ℕ):∀ i j:Fin w.length,j.val - i.val ≤ d → i < j →
  w[i.val].1 = w[j.val].1 → w[i.val].2 ≠ w[j.val].2 →
  ∃ k:Fin w.length,i < k ∧ k < j ∧ ¬L.Adj w[i.val].1 w[k.val].1 ∧ w[k.val].1 ≠ w[i.val].1:=by
 induction d with
 | zero=>intro i j hd hij; rw [Fin.lt_def] at hij; omega
 | succ d ih=>
  intro i j hd hij hv hb
  obtain ⟨k,hik,hkj,ha⟩:=H i j hij hv hb
  by_cases hk:w[k.val].1 = w[i.val].1
  ·by_cases hbk:w[i.val].2 = w[k.val].2
   ·obtain ⟨m,h1,h2,h3⟩:=ih k j (by rw [Fin.lt_def] at hik; omega) hkj (hk.trans hv) (hbk ▸ hb)
    exact ⟨m,hik.trans h1,h2,by rwa [hk] at h3⟩
   ·obtain ⟨m,h1,h2,h3⟩:=ih i k (by rw [Fin.lt_def] at hkj; omega) hik hk.symm hbk
    exact ⟨m,h1,h2.trans hkj,h3⟩
  ·exact ⟨k,hik,hkj,ha,hk⟩
theorem Dj (k:ℕ) (hk:k < w.length) (c:V) :
  cn w (k+1) c = cn w k c + if w[k].1 = c then 1 else 0:=by
 unfold cn; rw [← List.take_concat_get hk,List.concat_eq_append,List.countP_append]; simp
theorem Kq (k:ℕ) (hk:k < w.length) {s t:ℕ} (hs:s ≤ k) (ht:k < t):cn w s w[k].1 < cn w t w[k].1:=by
 have mono {s t:ℕ} (h:s ≤ t):cn w s w[k].1 ≤ cn w t w[k].1:=(List.take_sublist_take_left h).countP_le
 have h1:=Dj w k hk w[k].1
 rw [if_pos rfl] at h1
 have:=mono hs; have:=mono (show k+1 ≤ t by omega); omega
theorem F3 {s t:ℕ} {c:V} (h:cnt w s c = cnt w t c):cn w s c = cn w t c:=by
 have b (t):cn w t c < w.length+1:=Nat.lt_succ_of_le ((List.countP_le_length).trans (List.take_sublist _ _).length_le)
 unfold cnt at h; rwa [ZMod.natCast_eq_natCast_iff',Nat.mod_eq_of_lt (b s),Nat.mod_eq_of_lt (b t)] at h
theorem block (H:Barrier L w) (i j:Fin w.length) (hv:w[i.val].1 = w[j.val].1)
  (hf:Ek L w w[i.val].1 (cnt w i) (cnt w j)):w[i.val].2 = w[j.val].2:=by
 have key (i j:Fin w.length) (hij:i < j) (hv:w[i.val].1 = w[j.val].1)
   (hf:Ek L w w[i.val].1 (cnt w i) (cnt w j)):w[i.val].2 = w[j.val].2:=by
  by_contra hb
  obtain ⟨k,hik,hkj,ha,hne⟩:=strong L w H _ i j le_rfl hij hv hb
  have:=F3 w (hf _ hne ha)
  have:=Kq w k k.isLt (le_of_lt (Fin.lt_def.mp hik)) (Fin.lt_def.mp hkj); omega
 rcases lt_trichotomy i j with h|rfl|h
 ·exact key i j h hv hf
 ·rfl
 ·exact (key j i h hv.symm (fun c hc ha=>(hf c (hv ▸ hc) (hv ▸ ha)).symm)).symm
theorem Gz (H:Barrier L w) (i:Fin w.length) :
  (if w[i.val].2 then step L w w[i.val].1 else (step L w w[i.val].1)⁻¹) (cnt w i) = cnt w (i.val+1):=by
 have hsg:sgn L w w[i.val].1 (cnt w i) = w[i.val].2:=by
  have ex:∃ j:Fin w.length,w[j.val].1 = w[i.val].1 ∧ Ek L w w[i.val].1 (cnt w i) (cnt w j):=
   ⟨i,rfl,fun _ _ _=>rfl⟩
  unfold sgn; rw [dif_pos ex]
  obtain ⟨h1,h2⟩:=Classical.choose_spec ex
  exact (block L w H i _ h1.symm h2).symm
 have hc:cnt w (i.val+1) = Function.update (cnt w i) w[i.val].1 (cnt w i w[i.val].1 + 1):=by
  funext c; by_cases h:c = w[i.val].1
  ·subst h; simp [cnt,Dj w i i.isLt]
  ·simp [cnt,Dj w i i.isLt,h,Ne.symm h]
 rw [hc]; cases hb:w[i.val].2 <;> simp [step,hsg,hb,Equiv.Perm.inv_def]
end
end Counter
open Counter
variable {V:Type*} (L:SimpleGraph V)
private def lit (x:V × Bool):a1 L:=if x.2 then a0 L x.1 else (a0 L x.1)⁻¹
private def val (w:List (V × Bool)):=(w.map (lit L)).prod
@[local simp] private theorem F5 (p q:List (V × Bool)):val L (p++q) = val L p * val L q:=by simp [val]
@[local simp] private theorem val_cons (x) (w:List (V × Bool)):val L (x::w) = lit L x * val L w:=rfl
private theorem spell (g:a1 L):∃ w,val L w = g:=by
 induction g using PresentedGroup.induction_on with | H x=>
 induction x using FreeGroup.induction_on with
 | C1=>exact ⟨[],by simp [val]⟩
 | of x=>exact ⟨[(x,true)],by simp [val,lit,a0,PresentedGroup.of]⟩
 | inv_of x _=>exact ⟨[(x,false)],by simp [val,lit,a0,PresentedGroup.of]⟩
 | mul x y hx hy=>obtain ⟨p,hp⟩:=hx; obtain ⟨q,hq⟩:=hy; exact ⟨p++q,by simp [hp,hq]⟩
private theorem Dk (w:List (V × Bool)) (hm:∀ z,val L z = val L w → w.length ≤ z.length) :
  Barrier L w:=by
 intro i j hij hv hb
 by_contra! h
 let p:=w.take i.val
 let m:=(w.drop (i.val+1)).take (j.val-(i.val+1))
 let q:=w.drop (j.val+1)
 have hdist:i.val+1+(j.val-(i.val+1)) = j.val:=by omega
 have hs:p ++ w[i.val] :: (m ++ w[j.val] :: q) = w:=by
  have hm':=List.take_append_drop (j.val-(i.val+1)) (w.drop (i.val+1))
  rw [List.drop_drop,hdist,← List.getElem_cons_drop j.isLt] at hm'
  change p ++ w[i.val] :: ((w.drop _).take _ ++ w[j.val] :: w.drop _) = w
  rw [hm',List.getElem_cons_drop,List.take_append_drop]
 have mc:Commute (lit L w[i.val]) (val L m):=by
  apply Commute.list_prod_right; intro u hu
  obtain ⟨x,hx,rfl⟩:=List.mem_map.mp hu
  obtain ⟨k,hk,rfl⟩:=List.getElem_of_mem hx
  have hkl:i.val+1+k < w.length:=by simp [m] at hk; omega
  have hkj:i.val+1+k < j.val:=by simp [m] at hk; omega
  have ha:=a2 L (h ⟨i.val+1+k,hkl⟩ (by change i.val < i.val+1+k; omega) hkj)
  simp only [m,List.getElem_take,List.getElem_drop,lit]; split_ifs <;> first | exact ha | exact ha.inv_left | exact ha.inv_right | exact ha.inv_left.inv_right
 have opp:lit L w[j.val] = (lit L w[i.val])⁻¹:=by
  unfold lit; rw [hv]; cases hi:w[i.val].2 <;> cases hj:w[j.val].2 <;> simp_all
 have he:val L (p++m++q) = val L w:=by
  conv_rhs=>rw [← hs];
  simp only [F5,val_cons,opp]; rw [←mul_assoc (val L m),←mul_assoc (lit L _),←mul_assoc (lit L _),mc.mul_inv_cancel]; group
 have:=hm _ he
 have:=congrArg List.length hs
 simp only [List.length_append,List.length_cons] at *; omega
theorem wS (V:Type u) [Finite V] (L:SimpleGraph V):Group.ResiduallyFinite (a1 L):=by
 classical
 apply Group.residuallyFinite_of_forall_exists_finite_monoidHom
 intro g hg
 obtain ⟨z,hz⟩:=spell L g
 have ex:∃ n:ℕ,∃ w:List (V × Bool),val L w = g ∧ w.length = n:=⟨_,z,hz,rfl⟩
 obtain ⟨w,hw,hn⟩:=Nat.find_spec ex
 have H:Barrier L w:=Dk L w (by intro q hq; rw [hn]; exact Nat.find_min' ex ⟨q,hq.trans hw,rfl⟩)
 let f:=sW L (fun a=>(step L w a)⁻¹) (fun _ _ h=>(Jb L w h).inv_left.inv_right)
 have go (k:ℕ) (hk:k ≤ w.length):(f (val L (w.take k)))⁻¹ (cnt w 0) = cnt w k:=by
  induction k with
  | zero=>simp [val]
  | succ k ih=>
   have hs:=Gz L w H ⟨k,by omega⟩
   rw [← List.take_concat_get (by omega:k < w.length)]; simp only [List.concat_eq_append,F5,map_mul,mul_inv_rev,Equiv.Perm.mul_apply,ih (by omega)]
   change (f (lit L w[k] * 1))⁻¹ (cnt w k) = _
   cases h:w[k].2 <;> simpa [f,lit,h] using hs
 have hwpos:0 < w.length:=by by_contra! h; have:w = []:=List.length_eq_zero_iff.mp (by omega); subst w; exact hg (hw.symm.trans (by simp [val]))
 refine ⟨_,inferInstance,inferInstance,f,?_⟩
 intro hf
 have hall:=go w.length le_rfl
 simp only [List.take_length,hw,hf,inv_one,Equiv.Perm.one_apply] at hall
 have:=F3 w (congrFun hall w[0].1)
 have:=Kq w 0 hwpos le_rfl hwpos; omega
end EilenbergGanea
end
noncomputable section
open Classical Set
namespace EilenbergGanea
namespace TraceWords
variable {V:Type*} (L:SimpleGraph V)
abbrev a8 (V:Type*):=V × Bool
abbrev a9 (V:Type*):=List (a8 V)
def lX (x:a8 V):a8 V:=(x.1,!x.2)
@[simp] theorem s6 (x:a8 V):lX (lX x)=x:=by
 cases x; simp [lX]
def Independent (x y:a8 V):Prop:=L.Adj x.1 y.1
@[simp] theorem GO (x y:a8 V) :
  Independent L (lX x) y ↔ Independent L x y:=Iff.rfl
@[simp] theorem F6 (x y:a8 V) :
  Independent L x (lX y) ↔ Independent L x y:=Iff.rfl
@[simp] theorem JN (x:a8 V):¬ Independent L x x:=fun h=>L.irrefl h
theorem Independent.symm {x y:a8 V} (h:Independent L x y):Independent L y x:=
 L.symm.symm _ _ h
section RootCounts
variable [LinearOrder V]
def gY (s:Multiset (V × V)) (v:V):Finset V:=by
 classical
 exact ((s.filter (fun p=>¬ L.Adj p.1 v)).map Prod.snd).toFinset
def jC (s:Multiset (V × V)) (v:V):V:=
 if h:(gY L s v).Nonempty then (gY L s v).min' h else v
def d6 (s:Multiset (V × V)) (v:V):Multiset (V × V):=
 (v,jC L s v) ::ₘ s
def h6 (s:Multiset (V × V)) (w:a9 V):Multiset (V × V):=
 w.foldl (fun s x=>d6 L s x.1) s
@[simp] theorem RJ (s:Multiset (V × V)):h6 L s []=s:=rfl
@[simp] theorem Nz (s:Multiset (V × V)) (x:a8 V) (w:a9 V) :
  h6 L s (x :: w)=h6 L (d6 L s x.1) w:=rfl
theorem RK (s:Multiset (V × V)) (w v:a9 V) :
  h6 L s (w ++ v)=h6 L (h6 L s w) v:=List.foldl_append
variable {L}
theorem nL {s:Multiset (V × V)} {v r:V} :
  r ∈ gY L s v ↔ ∃ p ∈ s,¬ L.Adj p.1 v /\ p.2=r:=by
 classical
 simp only [gY,Multiset.mem_toFinset,Multiset.mem_map,Multiset.mem_filter]
 aesop
theorem RM (s:Multiset (V × V)) {a v:V}
  (r:V) (h:L.Adj a v) :
  gY L ((a,r) ::ₘ s) v=gY L s v:=by
 classical
 simp [gY,h]
theorem Kt (s:Multiset (V × V)) {a v:V}
  (r:V) (h:L.Adj a v) :
  jC L ((a,r) ::ₘ s) v=jC L s v:=by
 simp only [jC,RM s r h]
theorem RO (s:Multiset (V × V)) {v w:V} (h:L.Adj v w) :
    d6 L (d6 L s v) w=d6 L (d6 L s w) v:=by
  simp only [d6,Kt s _ h,
    Kt s _ (L.symm.symm _ _ h)]
  exact Multiset.cons_swap _ _ _
def iE (L:SimpleGraph V) (s:Multiset (V × V)):Prop:=
 (∀ p ∈ s,(p.2,p.2) ∈ s) /\
  ∀ p ∈ s,∀ q ∈ s,p.2 ≠ q.2 -> L.Adj p.2 q.2
theorem NA (s:Multiset (V × V)) (v:V) :
  (∃ p ∈ s,p.2=jC L s v) \/
   (jC L s v=v /\ ∀ p ∈ s,L.Adj p.1 v):=by
 classical
 by_cases h:(gY L s v).Nonempty
 ·left
  have hm:=Finset.min'_mem (gY L s v) h
  obtain ⟨p,hp,_,he⟩:=nL.mp hm
  exact ⟨p,hp,by simpa only [jC,dif_pos h] using he⟩
 ·refine Or.inr ⟨by simp [jC,h],?_⟩
  intro p hp
  by_contra hn
  exact h ⟨p.2,nL.mpr ⟨p,hp,hn,rfl⟩⟩
theorem iE.insert {s:Multiset (V × V)} (hs:iE L s) (v:V) :
  iE L (d6 L s v):=by
 classical
 have hr:(jC L s v,jC L s v) ∈ d6 L s v:=by
  rcases NA (L:=L) s v with ⟨p,hp,he⟩ | ⟨he,_⟩
  ·simp only [d6,Multiset.mem_cons]
   right
   rw [<- he]
   exact hs.1 p hp
  ·simp [d6,he]
 have ha:∀ p ∈ s,jC L s v ≠ p.2 -> L.Adj (jC L s v) p.2:=by
  intro p hp hne
  rcases NA (L:=L) s v with ⟨q,hq,he⟩ | ⟨he,hv⟩
  ·rw [<- he] at hne ⊢
   exact hs.2 q hq p hp hne
  ·rw [he]
   exact L.symm.symm _ _ (hv (p.2,p.2) (hs.1 p hp))
 constructor
 ·intro p hp
  rcases Multiset.mem_cons.mp hp with rfl | hp
  ·exact hr
  ·exact Multiset.mem_cons.mpr (Or.inr (hs.1 p hp))
 ·intro p hp q hq hne
  rcases Multiset.mem_cons.mp hp with rfl | hp
  ·rcases Multiset.mem_cons.mp hq with rfl | hq
   ·exact False.elim (hne rfl)
   ·exact ha q hq hne
  ·rcases Multiset.mem_cons.mp hq with rfl | hq
   ·exact L.symm.symm _ _ (ha p hp hne.symm)
   ·exact hs.2 p hp q hq hne
theorem iE.RP {s:Multiset (V × V)} (hs:iE L s) (w:a9 V) :
  iE L (h6 L s w):=by
 induction w generalizing s with
 | nil=>exact hs
 | cons x w ih=>exact ih (hs.insert x.1)
theorem co7 (w:a9 V):iE L (h6 L 0 w):=
 iE.RP ⟨by simp,by simp⟩ w
variable (L)
def jQ (s:Multiset (V × V)):V →₀ ℕ:=
 (s.map (fun p=>Finsupp.single p.2 1)).sum
def oQ (w:a9 V):V →₀ ℕ:=jQ (h6 L 0 w)
end RootCounts
end TraceWords
end EilenbergGanea
end
end OAI
end
namespace OAI.EilenbergGanea.TraceWords
noncomputable section
open Classical Set
variable {V:Type*} [LinearOrder V] (L:SimpleGraph V)
structure Pile (V:Type*) where
 stk:V → List (Option (Bool × V))
 beads:Multiset (V × V)
 charge:ℤ

theorem Pile.ext {s t : Pile V} (h : s.stk = t.stk) (k : s.beads = t.beads) (l : s.charge = t.charge) : s = t := by cases s; cases t; congr

def lY:Pile V:=⟨fun _=>[],0,0⟩
def weight (b:Bool):ℤ:=if b then 1 else -1
def push (s:Pile V) (v:V) (b:Bool):Pile V:=
 ⟨fun w=>if v = w then some (b,jC L s.beads v) :: s.stk w
  else if L.Adj v w then s.stk w else none :: s.stk w,
  d6 L s.beads v,s.charge + weight b⟩
def top (s:Pile V) (v:V):=((s.stk v).head?.join).map Prod.fst
@[simp] theorem El (s:Pile V) (v w:V) (b:Bool) :
  top (push L s v b) w = if v=w then some b else if L.Adj v w then top s w else none:=by
 classical
 by_cases h:v=w <;> by_cases k:L.Adj v w <;> simp [top,push,h,k]
theorem push_inj (v:V) (b:Bool):Function.Injective (fun s=>push L s v b):=by
 intro s t h
 have hr:=congrArg (fun p:Pile V=>p.stk v) h
 simp [push] at hr
 apply Pile.ext
 ·funext w
  have he:=congrArg (fun p:Pile V=>p.stk w) h
  by_cases hv:v=w
  ·subst w; exact hr.2
  ·by_cases ha:L.Adj v w <;> simpa [push,hv,ha] using he
 ·have he:=congrArg Pile.beads h
  simpa [push,d6,hr.1] using he
 ·simpa [push] using congrArg Pile.charge h
theorem Ak (s:Pile V) {v w:V} (h:L.Adj v w) (b c:Bool) :
  push L (push L s v b) w c = push L (push L s w c) v b:=by
 apply Pile.ext
 ·funext k
  by_cases hv:v=k <;> by_cases hw:w=k
  all_goals try subst k
  all_goals simp_all [push,d6,Kt _ _ h,Kt _ _ h.symm,h.ne,h.ne.symm,h.symm]
  split_ifs <;> rfl
 ·exact RO _ h
 ·simp [push,add_right_comm]
inductive Built:Pile V → Prop
 | nil:Built lY
 | snoc {s:Pile V} (hs:Built s) (v:V) (b:Bool) (ok:top s v ≠ some (!b)):Built (push L s v b)

theorem peel {s:Pile V} (hs:Built L s) (v:V) (b:Bool) (e:top s v = some b) :
  ∃ t,Built L t ∧ top t v ≠ some (!b) ∧ push L t v b = s:=by
 induction hs with
 | nil=>simp [top,lY] at e
 | @snoc s hs w c ok ih=>
  by_cases he:w=v
  ·subst w
   have hc:c=b:=by simpa using e
   subst c
   exact ⟨s,hs,ok,rfl⟩
  ·by_cases ha:L.Adj w v
   ·obtain ⟨t,ht,hn,eq⟩:=ih (by simpa [he,ha] using e)
    subst s
    have hok:top t w ≠ some (!c):=by simpa [Ne.symm he,ha.symm] using ok
    exact ⟨_,.snoc ht w c hok,by simpa [he,ha] using hn,Ak L t ha c b⟩
   ·simp [he,ha] at e
end
noncomputable section
open Classical Set
variable {V:Type*} [LinearOrder V] (L:SimpleGraph V)
def move (s:Pile V) (v:V) (b:Bool):Pile V:=
 if h:∃ t,push L t v (!b) = s then h.choose else push L s v b

theorem forward {s:Pile V} {v:V} {b:Bool} (h:top s v ≠ some (!b)) :
  move L s v b = push L s v b:=by
 unfold move
 split_ifs with e
 ·obtain ⟨_,rfl⟩:=e
  simp at h
 ·rfl
@[simp] theorem backward (s:Pile V) (v:V) (b:Bool) :
  move L (push L s v b) v (!b) = s:=by
 unfold move
 simp only [Bool.not_not]
 rw [dif_pos ⟨s,rfl⟩]
 apply push_inj L v b
 exact Classical.choose_spec (show ∃ t,push L t v b = push L s v b from ⟨s,rfl⟩)
theorem nO {s:Pile V} (hs:Built L s) (v:V) (b:Bool) :
  (top s v ≠ some (!b) ∧ move L s v b = push L s v b) ∨
  (Built L (move L s v b) ∧ top (move L s v b) v ≠ some b ∧ push L (move L s v b) v (!b) = s):=by
 by_cases h:top s v = some (!b)
 ·obtain ⟨t,ht,hn,rfl⟩:=peel L hs v (!b) h
  right
  rw [show move L (push L t v (!b)) v b = t by simpa using backward L t v (!b)]
  simpa using (show Built L t ∧ top t v ≠ some b ∧ push L t v (!b) = push L t v (!b) from ⟨ht,by simpa using hn,rfl⟩)
 ·exact Or.inl ⟨h,forward L h⟩
theorem GZ {s:Pile V} (hs:Built L s) (v:V) (b:Bool):Built L (move L s v b):=by
 rcases nO L hs v b with ⟨hn,he⟩ | ⟨ht,_⟩
 ·rw [he]; exact .snoc hs _ _ hn
 ·exact ht
theorem En {s:Pile V} (hs:Built L s) (v:V) (b:Bool):move L (move L s v b) v (!b) = s:=by
 rcases nO L hs v b with ⟨_,he⟩ | ⟨_,hn,he⟩
 ·rw [he,backward]
 ·rw [forward L (by simpa using hn),he]
theorem DJ {s:Pile V} (hs:Built L s) {v w:V} (h:L.Adj v w) (b c:Bool) :
  move L (push L s v b) w c = push L (move L s w c) v b:=by
 rcases nO L hs w c with ⟨hn,he⟩ | ⟨_,_,he⟩
 ·rw [forward L (by simpa [h.ne,h] using hn),he,Ak L s h]
 ·conv_lhs=>rw [← he,Ak L _ h.symm]
  simpa using backward L (push L (move L s w c) v b) w (!c)
theorem Fj {s:Pile V} (hs:Built L s) {v w:V} (h:L.Adj v w) (b c:Bool) :
  move L (move L s v b) w c = move L (move L s w c) v b:=by
 rcases nO L hs v b with ⟨hn,he⟩ | ⟨ht,_,he⟩
 ·rw [he,DJ L hs h]
  apply Eq.symm
  apply forward
  rcases nO L hs w c with ⟨_,hw⟩ | ⟨_,_,hw⟩
  ·simpa [hw,h.symm,h.ne.symm] using hn
  ·rwa [← hw,El,if_neg h.ne.symm,if_pos h.symm] at hn
 ·conv_rhs=>rw [← he,DJ L ht h]
  simpa using (backward L (move L (move L s v b) w c) v (!b)).symm
end
noncomputable section
open Classical Set
variable {V:Type*} [LinearOrder V] (L:SimpleGraph V)
section Evaluation
variable {K:Type*} [Group K] (f:V -> K)
def cQ (x:a8 V):K:=if x.2 then f x.1 else (f x.1)⁻¹
@[simp] theorem q2 (v:V):cQ f (v,true)=f v:=rfl
@[simp] theorem dm0 (v:V):cQ f (v,false)=(f v)⁻¹:=rfl
@[simp] theorem ae8 (x:a8 V):cQ f (lX x) =
  (cQ f x)⁻¹:=by
 rcases x with ⟨x,b⟩; cases b <;> simp [cQ,lX]
def kT (w:a9 V):K:=(w.map (cQ f)).prod
@[simp] theorem dv6:kT f []=1:=rfl
@[simp] theorem p6 (x:a8 V) (w:a9 V) :
  kT f (x :: w)=cQ f x * kT f w:=rfl
@[simp] theorem cx2 (w v:a9 V) :
  kT f (w ++ v)=kT f w * kT f v:=by simp [kT]
@[simp] theorem bb0 (x:a8 V):kT f [x]=cQ f x:=by
 simp
end Evaluation
abbrev qK:={s:Pile V // Built L s}
def turn (v:V) (b:Bool) (s:qK L):qK L:=⟨move L s.val v b,GZ L s.property v b⟩
def perm (v:V):Equiv.Perm (qK L) where
 toFun:=turn L v false
 invFun:=turn L v true
 left_inv s:=Subtype.ext (En L s.property v false)
 right_inv s:=Subtype.ext (En L s.property v true)
def F7:a1 L →* Equiv.Perm (qK L):=sW L (perm L) (by
 intro v w h
 ext s:1
 exact Subtype.ext (Fj L s.property h.symm false false))
def ride (s:qK L) (g:a1 L):qK L:=F7 L g⁻¹ s
@[simp] theorem JO (s:qK L):ride L s 1 = s:=by simp [ride]
theorem yQ (s:qK L) (g k:a1 L):ride L s (g*k) = ride L (ride L s g) k:=by simp [ride]
@[simp] theorem wT (s:qK L) (x:a8 V):ride L s (cQ (a0 L) x) = turn L x.1 x.2 s:=by
 rcases x with ⟨v,b⟩; cases b <;> simp [ride,cQ,F7] <;> rfl
def jS:=ride L ⟨lY,.nil⟩
theorem G7 (g:a1 L) (x:a8 V):jS L (g*cQ (a0 L) x) = turn L x.1 x.2 (jS L g):=by rw [jS,yQ,wT]
end
noncomputable section
open Classical Set
variable {V:Type*} [LinearOrder V] (L:SimpleGraph V)
omit [LinearOrder V] in
@[simp] theorem Je (p:V × V) (s:Multiset (V × V)) :
  jQ (p ::ₘ s)=Finsupp.single p.2 1 + jQ s:=by
 simp [jQ]
omit [LinearOrder V] in
@[simp] theorem ds7:jQ (0:Multiset (V × V))=0:=by
 simp [jQ]
theorem bb2 (w:a9 V) (x:a8 V) :
  oQ L (w ++ [x])=oQ L w +
   Finsupp.single (jC L (h6 L 0 w) x.1) 1:=by
 simp only [oQ,RK,Nz,RJ,d6,Je]
 exact add_comm _ _
omit [LinearOrder V] in
 theorem ND (s:Multiset (V × V)) (r:V) :
    jQ s r ≠ 0 ↔ ∃ p ∈ s,p.2=r:=by
  classical
  induction s using Multiset.induction_on with
  | empty=>simp
  | cons p s ih=>
      by_cases hp:p.2=r
      · simp [Je,hp]
      · simp [Je,hp,ih]
omit [LinearOrder V] in
 theorem RQ {s:Multiset (V × V)} (hs:iE L s) :
    ((jQ s).support:Set V).Pairwise L.Adj:=by
  intro r hr t ht hne
  obtain ⟨p,hp,hpr⟩:=(ND s r).mp (Finsupp.mem_support_iff.mp hr)
  obtain ⟨q,hq,hqt⟩:=(ND s t).mp (Finsupp.mem_support_iff.mp ht)
  rw [<- hpr,<- hqt] at hne ⊢
  exact hs.2 p hp q hq hne
omit [LinearOrder V] in
 theorem RU [Fintype V] (s:Multiset (V × V)) :
    ∑ v,jQ s v=s.card:=by
  classical
  induction s using Multiset.induction_on with
  | empty=>simp
  | cons p s ih=>
      simp [Je,Finset.sum_add_distrib,ih,Finsupp.single_apply,add_comm]
omit [LinearOrder V] in
 theorem RV (c:V →₀ ℕ) (r:V) :
    c.support ⊆ (c + Finsupp.single r 1).support:=by
  intro v hv
  apply Finsupp.mem_support_iff.mpr
  intro h
  apply Finsupp.mem_support_iff.mp hv
  exact (Nat.add_eq_zero_iff.mp (show c v + (Finsupp.single r 1) v=0 from h)).1
theorem invariant {s:Pile V} (h:Built L s):iE L s.beads:=by
 induction h with
 | nil=>exact ⟨by simp [lY],by simp [lY]⟩
 | snoc _ _ _ _ ih=>exact ih.insert _
abbrev Trace:={s:Multiset (V × V) // iE L s}
def observe (s:qK L):Trace L:=⟨s.val.beads,invariant L s.property⟩
def cE (g:a1 L):=observe L (jS L g)
def b2 (s:Trace L):=s.val.card
def gO (s:Trace L):=jQ s.val
def grow (s:Trace L) (x:a8 V):Trace L:=⟨d6 L s.val x.1,s.property.insert _⟩
theorem p9 (s:Trace L):((gO L s).support:Set V).Pairwise L.Adj:=RQ L s.property
theorem Lb [Fintype V] (s:Trace L):∑ v,gO L s v = b2 L s:=RU s.val
theorem g8 (t:Trace L) (x:a8 V):b2 L (grow L t x) = b2 L t + 1:=Multiset.card_cons _ _
theorem z6 (s:Trace L) (x:a8 V):∃ r,gO L (grow L s x) = gO L s + Finsupp.single r 1:=
 ⟨_,(Je _ _).trans (add_comm _ _)⟩
theorem RY (s:Trace L) (x:a8 V):(gO L s).support ⊆ (gO L (grow L s x)).support:=by
 obtain ⟨r,hr⟩:=z6 L s x
 rw [hr]; exact RV _ _
theorem j2 (g:a1 L) (x:a8 V):cE L (g * cQ (a0 L) x) = grow L (cE L g) x ∨
  cE L g = grow L (cE L (g * cQ (a0 L) x)) (lX x):=by
 unfold cE
 rw [G7]
 rcases nO L (jS L g).property x.1 x.2 with ⟨_,he⟩ | ⟨_,_,he⟩
 ·exact Or.inl (Subtype.ext (congrArg Pile.beads he))
 ·exact Or.inr (Subtype.ext (congrArg Pile.beads he.symm))
variable [Fintype V]
def iJ (t:Trace L) (v:V):ℝ:=
 (gO L t v:ℝ) / (b2 L t:ℝ)
def dW (g:a1 L):V -> ℝ:=
 iJ L (cE L g)
omit [Fintype V] in
theorem RZ (t:Trace L) (v:V):0 <= iJ L t v:=
 div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
theorem Ao {t:Trace L} (ht:0 < b2 L t) :
  ∑ v,iJ L t v=1:=by
 simp only [iJ,<- Finset.sum_div,<- Nat.cast_sum,Lb]
 exact div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt ht))
theorem vE (c:V →₀ ℕ) (r:V) {n:ℕ}
    (hn:0 < n) (hs:∑ v,c v=n) :
    ∑ v,|((c + Finsupp.single r 1:V →₀ ℕ) v:ℝ) / (n + 1:ℝ) -
      (c v:ℝ) / (n:ℝ)| <= 2 / (n + 1:ℝ):=by
  classical
  have hn0:(n:ℝ) ≠ 0:=Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hd:0 < (n + 1:ℝ):=by positivity
  have hi (v:V) :
      ((c + Finsupp.single r 1:V →₀ ℕ) v:ℝ) / (n + 1:ℝ) - (c v:ℝ) / (n:ℝ) =
      (((Finsupp.single r (1:ℕ)) v:ℝ) - (c v:ℝ) / n) / (n + 1:ℝ):=by
    simp only [Finsupp.add_apply,Nat.cast_add]
    field_simp [hn0,ne_of_gt hd]
    ring
  have hpoint (v:V) :
      |((c + Finsupp.single r 1:V →₀ ℕ) v:ℝ) / (n + 1:ℝ) - (c v:ℝ) / (n:ℝ)| <=
      (((Finsupp.single r (1:ℕ)) v:ℝ) + (c v:ℝ) / n) / (n + 1:ℝ):=by
    rw [hi,abs_div,abs_of_pos hd]
    apply div_le_div_of_nonneg_right _ hd.le
    calc
      _ <= |(((Finsupp.single r (1:ℕ)) v:ℝ))| + |(c v:ℝ) / n|:=
        abs_sub _ _
      _=_:=by rw [abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))]
  calc
    _ <= ∑ v,(((Finsupp.single r (1:ℕ)) v:ℝ) + (c v:ℝ) / n) /
        (n + 1:ℝ):=Finset.sum_le_sum (fun v _=>hpoint v)
    _=2 / (n + 1:ℝ):=by
      rw [<- Finset.sum_div,Finset.sum_add_distrib,<- Finset.sum_div]
      simp only [<- Nat.cast_sum,hs]
      norm_num [Finsupp.single_apply,div_self hn0]
theorem NG (t:Trace L) (x:a8 V)
  (ht:0 < b2 L t) :
  ∑ v,|iJ L (grow L t x) v - iJ L t v| <=
   2 / (b2 L t + 1:ℝ):=by
 obtain ⟨r,hr⟩:=z6 L t x
 simp only [iJ,g8,hr,Nat.cast_add,Nat.cast_one]
 exact vE (gO L t) r ht (Lb L t)
omit [Fintype V] in
theorem t7 (t:Trace L) (x:a8 V) :
  (((gO L t).support ∪
   (gO L (grow L t x)).support:Finset V):Set V).Pairwise L.Adj:=by
 rw [Finset.union_eq_right.mpr (RY L t x)]
 exact p9 L _
theorem R5 (g:a1 L) (x:a8 V)
  (hg:0 < b2 L (cE L g))
  (hgx:0 < b2 L (cE L
   (g * cQ (a0 L) x))) :
  let t:=cE L g
  let t':=cE L (g * cQ (a0 L) x)
  (((gO L t).support ∪ (gO L t').support:Finset V):Set V).Pairwise L.Adj /\
  ∃ n:ℕ,0 < n /\
   ((b2 L t=n /\ b2 L t'=n + 1) \/
    (b2 L t'=n /\ b2 L t=n + 1)) /\
   ∑ v,|dW L (g * cQ (a0 L) x) v -
    dW L g v| <= 2 / (n + 1:ℝ):=by
 dsimp only
 rcases j2 L g x with h | h
 ·rw [h] at hgx ⊢
  refine ⟨t7 L _ x,
   b2 L (cE L g),hg,Or.inl ⟨rfl,?_⟩,?_⟩
  ·exact g8 L _ x
  ·simpa only [dW,h] using
    NG L (cE L g) x hg
 ·rw [h] at hg ⊢
  refine ⟨?_,b2 L (cE L
   (g * cQ (a0 L) x)),hgx,Or.inr ⟨rfl,?_⟩,?_⟩
  ·rw [Finset.union_comm]
   exact t7 L _ _
  ·exact g8 L _ _
  ·simpa only [dW,h,abs_sub_comm] using
    NG L
     (cE L (g * cQ (a0 L) x)) (lX x) hgx
end
noncomputable section
open Classical Set
variable {V:Type*} [LinearOrder V] (L:SimpleGraph V)
@[simp] theorem a4 (v:V) :
  height L (a0 L v)=Multiplicative.ofAdd 1:=PresentedGroup.toGroup.of _
theorem shift (s:qK L) (v:V) (b:Bool):(turn L v b s).val.charge = s.val.charge + weight b:=by
 change (move L s.val v b).charge = _
 rcases nO L s.property v b with ⟨_,he⟩ | ⟨_,_,he⟩
 ·rw [he]; rfl
 ·have h:=congrArg Pile.charge he
  change (move L s.val v b).charge + weight (!b) = s.val.charge at h
  cases b <;> simp [weight] at * <;> omega

theorem D4 (g:a1 L):∀ s:qK L,(ride L s g).val.charge = s.val.charge + (height L g).toAdd:=by
  let S:Subgroup (a1 L):={
    carrier:={g | ∀ s:qK L,(ride L s g).val.charge = s.val.charge + (height L g).toAdd}
    one_mem':=by intro s; simp
    mul_mem':=by intro g k hg hk s; rw [yQ,hk,hg,map_mul]; exact add_assoc _ _ _
    inv_mem':=by
      intro g hg s
      have h:=hg (ride L s g⁻¹)
      rw [← yQ,inv_mul_cancel,JO] at h
      rw [map_inv]; exact eq_sub_of_add_eq h.symm |>.trans (sub_eq_add_neg ..) }
  apply PresentedGroup.generated_by _ S _ g
  intro v s
  change (ride L s (cQ (a0 L) (v,true))).val.charge = _
  rw [wT,shift]
  change _ = _ + (height L (a0 L v)).toAdd
  rw [a4]; rfl

theorem Eo {s:Pile V} (hs:Built L s):|s.charge| ≤ (s.beads.card:ℤ):=by
 induction hs with
 | nil=>simp [lY]
 | snoc _ v b _ ih=>
  change |_ + weight b| ≤ ((d6 L _ v).card:ℤ)
  simp only [d6,Multiset.card_cons,Nat.cast_add,Nat.cast_one]
  cases b <;> simp [weight,abs_le] at * <;> omega

theorem R6 (g:a1 L):|(height L g).toAdd| ≤ (b2 L (cE L g):ℤ):=by
 have h:=D4 L g ⟨lY,.nil⟩
 change (jS L g).val.charge = 0 + _ at h
 rw [zero_add] at h
 rw [← h]; exact Eo L (jS L g).property
theorem R7 {s:Multiset (V × V)} {v:V}
  (hs:∀ p ∈ s,p.2=p.1) (hv:∀ p ∈ s,p.1=v \/ L.Adj p.1 v) :
  jC L s v=v:=by
 classical
 unfold jC
 split_ifs with h
 ·obtain ⟨p,hp,hdep,hroot⟩:=nL.mp (Finset.min'_mem _ h)
  rw [<- hroot,hs p hp]
  exact (hv p hp).resolve_right hdep
 ·rfl
theorem CH {C:Set V} (hC:C.Pairwise L.Adj)
  {s:Multiset (V × V)} (hs:∀ p ∈ s,p.1 ∈ C /\ p.2=p.1)
  {w:a9 V} (hw:∀ x ∈ w,x.1 ∈ C) :
  h6 L s w=((w.map (fun x=>(x.1,x.1))):Multiset (V × V)) + s:=by
 classical
 induction w generalizing s with
 | nil=>simp
 | cons x w ih=>
   have hx:x.1 ∈ C:=hw x (by simp)
   have hr:jC L s x.1=x.1:=by
    apply R7 L (fun p hp=>(hs p hp).2)
    intro p hp
    by_cases hpv:p.1=x.1
    ·exact Or.inl hpv
    ·exact Or.inr (hC (hs p hp).1 hx hpv)
   have hi:∀ p ∈ d6 L s x.1,p.1 ∈ C /\ p.2=p.1:=by
    intro p hp
    simp only [d6,hr,Multiset.mem_cons] at hp
    rcases hp with rfl | hp
    ·exact ⟨hx,rfl⟩
    ·exact hs p hp
   rw [Nz,ih hi (fun y hy=>hw y (List.mem_cons_of_mem _ hy))]
   simp [d6,hr,<- Multiset.cons_coe,Multiset.add_cons]
theorem R8 {C:Set V} (hC:C.Pairwise L.Adj)
  {w:a9 V} (hw:∀ x ∈ w,x.1 ∈ C) :
  oQ L w=(w.map (fun x=>Finsupp.single x.1 (1:ℕ))).sum:=by
 rw [oQ,CH L hC (by simp) hw]
 simp only [add_zero,jQ,Multiset.map_coe,List.map_map,Multiset.sum_coe,Function.comp_def]
theorem D5 (w:a9 V) (hw:∀ x ∈ w,x.2=false) (s:qK L) (hn:∀ v,top s.val v ≠ some true) :
  (ride L s (kT (a0 L) w)).val.beads = h6 L s.val.beads w:=by
 induction w generalizing s with
 | nil=>simp
 | cons x xs ih=>
  have hx:=hw x (by simp)
  have he:(turn L x.1 x.2 s).val = push L s.val x.1 x.2:=forward L (by simpa [hx] using hn x.1)
  rw [p6,yQ,wT,ih (fun y hy=>hw y (List.mem_cons_of_mem _ hy)),he]; rfl
  intro v
  rw [he,El,hx]; split_ifs <;> simp [hn]
theorem lK {q r:V} (hqr:L.Adj q r) (n m:ℕ) :
  gO L (cE L
   ((a0 L q)⁻¹ ^ n * (a0 L r)⁻¹ ^ m)) =
   Finsupp.single q n + Finsupp.single r m:=by
 classical
 let w:a9 V:=List.replicate n (q,false) ++ List.replicate m (r,false)
 have hn:∀ x ∈ w,x.2=false:=by
  intro x hx
  simp only [w,List.mem_append,List.mem_replicate] at hx
  rcases hx with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> rfl
 have hC:({q,r}:Set V).Pairwise L.Adj:=by
  intro a ha b hb hab
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  ·exact False.elim (hab rfl)
  ·exact hqr
  ·exact L.symm.symm _ _ hqr
  ·exact False.elim (hab rfl)
 have hwc:∀ x ∈ w,x.1 ∈ ({q,r}:Set V):=by
  intro x hx
  simp only [w,List.mem_append,List.mem_replicate] at hx
  rcases hx with ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp
 have he:kT (a0 L) w =
   (a0 L q)⁻¹ ^ n * (a0 L r)⁻¹ ^ m:=by
  simp [kT,w,List.map_replicate]
 rw [← he]
 change jQ (ride L ⟨lY,.nil⟩ (kT (a0 L) w)).val.beads = _
 rw [D5 L w hn _ (by simp [lY,top])]
 change oQ L w = _
 rw [R8 L hC hwc]
 ext v
 simp [w,List.map_replicate,Finsupp.single_apply]
variable [Fintype V]
theorem R9 {q r:V} (hqr:L.Adj q r) (n m:ℕ) :
  b2 L (cE L
   ((a0 L q)⁻¹ ^ n * (a0 L r)⁻¹ ^ m))=n + m:=by
 rw [<- Lb,lK L hqr]
 simp [Finsupp.single_apply,Finset.sum_add_distrib]
theorem j0 {q r:V} (hqr:L.Adj q r)
    (n m:ℕ) (v:V) :
    dW L ((a0 L q)⁻¹ ^ n * (a0 L r)⁻¹ ^ m) v =
      ((if q=v then n else 0:ℕ) + (if r=v then m else 0:ℕ):ℝ) / (n + m:ℝ):=by
  rw [dW,iJ,lK L hqr,
    R9 L hqr]
  simp only [Finsupp.add_apply,Finsupp.single_apply,Nat.cast_add,Nat.cast_ite,Nat.cast_zero]
end
end OAI.EilenbergGanea.TraceWords
section
namespace OAI
noncomputable section
open Classical Set
namespace CubicalChains.HeightFiltration
open Classical
variable {G A:Type*} [Group G] [LinearOrder A] (L:SimpleGraph A)
variable (K:SimplicialChains.Contraction L)
def embed (g:G):SimplicialChains.Chains A →ₗ[ℤ] Chains G A:=
 Finsupp.lmapDomain ℤ ℤ (fun w=>(g,w))
omit [Group G] [LinearOrder A] in
@[simp] theorem Ku (g:G) (w:List A) (n:ℤ) :
  embed g (Finsupp.single w n)=Finsupp.single (g,w) n:=by simp [embed]
omit [Group G] [LinearOrder A] in
theorem Sb (g:G) (a:A) (c:SimplicialChains.Chains A) :
  embed g (SimplicialChains.front a c)=front a (embed g c):=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]
 | single w n=>simp
omit [Group G] [LinearOrder A] in
theorem wL (g:G) (w:List A) :
    kP g w=-embed g (SimplicialChains.cP w):=by
  induction w with
  | nil=>simp
  | cons a w ih=>
    simp only [z2,SimplicialChains.dK,map_sub,Ku,
      Sb,ih,map_neg]
    abel
omit [Group G] [LinearOrder A] in
theorem Fk (g:G) (c:SimplicialChains.Chains A) :
  upper (embed g c)=-embed g (SimplicialChains.boundary c):=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]; abel
 | single w n=>simp [wL,smul_neg]
def iF (h:G -> ℤ) (g:G) (w:List A):Chains G A:=
 if h g < 0 then -embed g (K.homotopy (Finsupp.single w 1)) else 0
def homotopy (h:G -> ℤ):Chains G A →ₗ[ℤ] Chains G A:=
 Finsupp.linearCombination ℤ (fun p=>iF L K h p.1 p.2)
omit [Group G] in
@[simp] theorem m2 (h:G -> ℤ) (g:G) (w:List A) (n:ℤ) :
  homotopy L K h (Finsupp.single (g,w) n)=n • iF L K h g w:=by simp [homotopy]
omit [Group G] in
theorem Dl (h:G -> ℤ) (g:G) (c:SimplicialChains.Chains A) :
  homotopy L K h (embed g c)=if h g < 0 then -embed g (K.homotopy c) else 0:=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>
  simp only [map_add,hc,hd]
  split
  ·simp_all
   abel
  ·simp_all
 | single w n=>
  simp only [Ku,m2,iF]
  split
  ·rw [show Finsupp.single w n=n • Finsupp.single w 1 by simp]
   simp only [map_smul,smul_neg]
  ·simp
omit [Group G] in
theorem Sd (h:G -> ℤ) (g:G) (w:List A)
  (hw:SimplicialChains.Valid L w) (hg:h g < 0) :
  upper (iF L K h g w) + homotopy L K h (kP g w) =
   Finsupp.single (g,w) 1:=by
 simp only [iF,if_pos hg,map_neg,Fk,wL,Dl]
 simp only [neg_neg]
 rw [<- map_add,K.identity w hw,Ku]
def above (h:G -> ℤ) (k:ℕ) (m:ℤ):Submodule ℤ (Chains G A):=
 Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 /\ p.2.length=k /\ m <= h p.1}
omit [Group G] in
theorem Jg (h:G -> ℤ) {k:ℕ} {m n:ℤ} (hmn:m <= n) :
  above L h k n <= above L h k m:=by
 apply Finsupp.supported_mono
 intro p hp
 exact ⟨hp.1,hp.2.1,hmn.trans hp.2.2⟩
omit [Group G] in
theorem Se (h:G -> ℤ) (g:G) {k:ℕ} (c:SimplicialChains.Chains A)
  (hc:c ∈ SimplicialChains.chains L k):embed g c ∈ above L h k (h g):=by
 apply d8 (embed g) _ _ _ hc
 intro w hw
 rw [Ku]
 exact Finsupp.single_mem_supported ℤ 1 ⟨hw.1,hw.2,le_refl _⟩
omit [Group G] in
theorem NR (h:G -> ℤ) (g:G) (w:List A)
  (hw:SimplicialChains.Valid L w):iF L K h g w ∈ above L h (w.length+1) (h g):=by
 unfold iF
 split
 ·apply Submodule.neg_mem
  apply Se
  exact K.degree _ _ (Finsupp.single_mem_supported ℤ 1 ⟨hw,rfl⟩)
 ·exact Submodule.zero_mem _
omit [Group G] in
theorem NU (h:G -> ℤ) {k:ℕ} {m:ℤ} {c:Chains G A}
  (hc:c ∈ above L h k m):homotopy L K h c ∈ above L h (k+1) m:=by
 apply d8 (homotopy L K h) _ _ _ hc
 rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
 dsimp at hw hl hh ⊢
 rw [m2,one_smul]
 have ht:=NR L K h g w hw
 rw [hl] at ht
 exact Jg L h hh ht
variable (v:A -> G) (h:G -> ℤ)
variable (hv:∀ g a,h (g * v a)=h g + 1)
include hv in
theorem wM (g:G) (w:List A) (hw:SimplicialChains.Valid L w) :
  kB v g w ∈ above L h (w.length-1) (h g+1):=by
 apply Finsupp.supported_mono _ (Ry v g w)
 rintro ⟨g',u⟩ ⟨a,ha,rfl⟩
 exact ⟨SimplicialChains.zP hw ha.sublist,by have:=ha.length; omega,
  by dsimp; rw [hv]⟩
include hv in
theorem BW {k:ℕ} {m:ℤ} {c:Chains G A}
  (hc:c ∈ above L h k m):lower v c ∈ above L h (k-1) (m+1):=by
 apply d8 (lower v) _ _ _ hc
 rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
 dsimp at hw hl hh ⊢
 rw [co2,one_smul]
 have ht:=wM L v h hv g w hw
 rw [hl] at ht
 exact Jg L h (by omega) ht
omit [Group G] in
theorem Fo {k:ℕ} {m:ℤ} {c:Chains G A}
  (hc:c ∈ above L h k m):upper c ∈ above L h (k-1) m:=by
 apply d8 (upper) _ _ _ hc
 rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
 dsimp at hw hl hh ⊢
 rw [Rw,one_smul]
 apply Finsupp.supported_mono _ (m8 g w)
 rintro ⟨g',u⟩ ⟨rfl,hs,he⟩
 dsimp at hl he hh ⊢
 exact ⟨SimplicialChains.zP hw hs,by omega,hh⟩
include hv in
theorem m5 {k:ℕ} {m:ℤ} {c:Chains G A}
  (hc:c ∈ above L h k m):boundary v c ∈ above L h (k-1) m:=by
 have he:boundary v c=lower v c + upper c:=by simp [lower]
 rw [he]
 exact Submodule.add_mem _ (Jg L h (show m <= m+1 by omega) (BW L v h hv hc))
  (Fo L h hc)
omit [Group G] in
theorem Lc {k:ℕ} {c:Chains G A} (hc:c ∈ above L h k 0) :
  homotopy L K h c=0:=by
 rw [above,Finsupp.supported_eq_span_single] at hc
 change c ∈ LinearMap.ker _
 apply Submodule.span_le.mpr _ hc
 rintro _ ⟨⟨g,w⟩,⟨_,_,hh⟩,rfl⟩
 simp [LinearMap.mem_ker,iF,not_lt.mpr hh]
def push:Chains G A →ₗ[ℤ] Chains G A:=
 LinearMap.id - (boundary v).comp (homotopy L K h) - (homotopy L K h).comp (boundary v)
theorem Ld (c:Chains G A):push L K v h c =
  c - boundary v (homotopy L K h c) - homotopy L K h (boundary v c):=rfl
theorem yT (g:G) (w:List A) (hw:SimplicialChains.Valid L w)
  (hg:h g < 0):push L K v h (Finsupp.single (g,w) 1) =
   - lower v (iF L K h g w) - homotopy L K h (kB v g w):=by
 have hu:=Sd L K h g w hw hg
 have he:boundary v (iF L K h g w) =
   lower v (iF L K h g w) + upper (iF L K h g w):=by
  simp [lower]
 have he':cP v g w=kB v g w + kP g w:=by simp [kB]
 simp only [Ld,m2,one_smul,gI]
 rw [he,he',map_add,<- hu]
 abel
include hv in
theorem Sh (g:G) (w:List A)
    (hw:SimplicialChains.Valid L w) (hg:0 <= h g) :
    push L K v h (Finsupp.single (g,w) 1)=Finsupp.single (g,w) 1:=by
  have hc:Finsupp.single (g,w) (1:ℤ) ∈ above L h w.length 0:=
    Finsupp.single_mem_supported ℤ 1 ⟨hw,rfl,hg⟩
  rw [Ld,Lc L K h hc,map_zero,
    Lc L K h (m5 L v h hv hc)]
  simp
include hv in
theorem G8 {k N:ℕ} (hk:0 < k) {c:Chains G A}
  (hc:c ∈ above L h k (-(N+1:ℕ):ℤ)) :
  push L K v h c ∈ above L h k (-(N:ℤ)):=by
 apply d8 (push L K v h) _ _ _ hc
 rintro ⟨g,w⟩ ⟨hw,hl,hh⟩
 dsimp at hw hl hh ⊢
 by_cases hg:h g < 0
 ·rw [yT L K v h g w hw hg]
  apply Submodule.sub_mem
  ·apply Submodule.neg_mem
   have ht:=BW L v h hv (NR L K h g w hw)
   simp only [Nat.add_sub_cancel] at ht
   rw [hl] at ht
   exact Jg L h (by norm_num at hh ⊢; omega) ht
  ·have ht:=NU L K h (wM L v h hv g w hw)
   have he:w.length-1+1=k:=by omega
   rw [he] at ht
   exact Jg L h (by norm_num at hh ⊢; omega) ht
 ·rw [Sh L K v h hv g w hw (not_lt.mp hg)]
  exact Finsupp.single_mem_supported ℤ 1 ⟨hw,hl,by change -(N:ℤ) <= h g; omega⟩
variable (comm:∀ a b,L.Adj a b -> Commute (v a) (v b))
include comm in
theorem r6 {k:ℕ} {m:ℤ} {c:Chains G A}
  (hc:c ∈ above L h k m):boundary v (boundary v c)=0:=by
 rw [above,Finsupp.supported_eq_span_single] at hc
 apply Submodule.span_induction (p:=fun c _=>boundary v (boundary v c)=0) _ _ _ _ hc
 ·rintro _ ⟨⟨g,w⟩,⟨hw,_,_⟩,rfl⟩
  simp only [gI,one_smul]
  exact qE v g w (hw.2.imp (fun {_ _} ha=>comm _ _ ha))
 ·simp
 ·intro c d _ _ hc hd; simp only [map_add,hc,hd,add_zero]
 ·intro n c _ hc; simp only [map_smul,hc,smul_zero]
include comm in
theorem Sl {k:ℕ} {m:ℤ} {c:Chains G A}
    (hc:c ∈ above L h k m) (hd:boundary v c ∈ above L h (k-1) 0) :
    boundary v (push L K v h c)=boundary v c:=by
  rw [Ld,map_sub,map_sub,Lc L K h hd,map_zero,
    r6 L v h comm (NU L K h hc)]
  simp
include K hv comm in
theorem Sm {k:ℕ} (hk:0 < k) (N:ℕ) (c:Chains G A)
  (hc:c ∈ above L h k (-(N:ℤ)))
  (hd:boundary v c ∈ above L h (k-1) 0) :
  ∃ b ∈ above L h k 0,boundary v b=boundary v c:=by
 induction N generalizing c with
 | zero=>exact ⟨c,by simpa using hc,rfl⟩
 | succ N ih=>
  have hp:=G8 L K v h hv hk hc
  have he:=Sl L K v h comm hc hd
  obtain ⟨b,hb,hdb⟩:=ih (push L K v h c) hp (by rwa [he])
  exact ⟨b,hb,hdb.trans he⟩
def total (k:ℕ):Submodule ℤ (Chains G A):=
 Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 /\ p.2.length=k}
omit [Group G] in
theorem Jh {k:ℕ} {m:ℤ} {c:Chains G A} (hc:c ∈ above L h k m) :
  c ∈ total (G:=G) L k:=by
 apply Finsupp.supported_mono _ hc
 intro p hp
 exact ⟨hp.1,hp.2.1⟩
omit [Group G] in
theorem oI {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
  ∃ N:ℕ,c ∈ above L h k (-(N:ℤ)):=by
 refine ⟨c.support.sup (fun p=>(-h p.1).toNat),?_⟩
 apply (Finsupp.mem_supported ℤ c).mpr
 intro p hp
 have ht:=(Finsupp.mem_supported ℤ c).mp hc hp
 have hb:=Finset.le_sup (f:=fun p=>(-h p.1).toNat) hp
 have hi:=Int.self_le_toNat (-h p.1)
 exact ⟨ht.1,ht.2,by omega⟩
include K hv comm in
theorem o9
  (exactTotal:∀ {k:ℕ},0 < k -> ∀ c,c ∈ total (G:=G) L k -> boundary v c=0 ->
   ∃ b ∈ total (G:=G) L (k+1),boundary v b=c)
  {k:ℕ} (hk:0 < k) (c:Chains G A) (hc:c ∈ above L h k 0)
  (hz:boundary v c=0) :
  ∃ b ∈ above L h (k+1) 0,boundary v b=c:=by
 obtain ⟨b,hb,hdb⟩:=exactTotal hk c (Jh L h hc) hz
 obtain ⟨N,hN⟩:=oI L h hb
 obtain ⟨b',hb',hdb'⟩:=Sm L K v h hv comm (by omega) N b hN
  (by simpa [hdb] using hc)
 exact ⟨b',hb',hdb'.trans hdb⟩
end CubicalChains.HeightFiltration
namespace CubicalChains.Reflection
variable {G A:Type*} [Group G] (v:A -> G)
def mirror:Chains G A →ₗ[ℤ] Chains G A:=
 Finsupp.linearCombination ℤ fun p=> (-1:ℤ)^p.2.length •
  Finsupp.single (p.1*(p.2.map (fun a=>(v a)⁻¹)).prod,p.2) 1
@[simp] theorem nT (g:G) (w:List A) (n:ℤ) :
  mirror v (Finsupp.single (g,w) n)=n • ((-1:ℤ)^w.length •
   Finsupp.single (g*(w.map (fun a=>(v a)⁻¹)).prod,w) 1):=by simp [mirror]
theorem Ep (x:A) (c:Chains G A) :
  mirror v (front x c)= -front x (mirror v (shift (fun a=>(v a)⁻¹) x c)):=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]; abel
 | single p n=>rcases p with ⟨g,w⟩; simp only [jO,nT,Ja,map_smul,List.map_cons,List.prod_cons,List.length_cons,pow_succ,mul_neg,mul_one,neg_smul,smul_neg,mul_assoc]
theorem NV (a:A) (w:List A) (hw:∀ b ∈ w,Commute (v a) (v b)) :
  Commute (v a) (w.map v).prod:=by
 apply Commute.list_prod_right
 intro x hx
 obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hx
 exact hw b hb
theorem prod_inv (w:List A) (hw:w.Pairwise (fun a b=>Commute (v a) (v b))) :
  (w.map (fun a=>(v a)⁻¹)).prod=(w.map v).prod⁻¹:=by
 induction w with
 | nil=>simp
 | cons a w ih=>
  obtain ⟨ha,hw⟩:=List.pairwise_cons.mp hw
  simp only [List.map_cons,List.prod_cons,ih hw,mul_inv_rev]
  exact (NV v a w ha).inv_left.inv_right.eq
theorem z8 (g:G) (w:List A)
    (hw:w.Pairwise (fun a b=>Commute (v a) (v b))) :
    mirror v (cP (fun a=>(v a)⁻¹) g w) =
      boundary v (mirror v (Finsupp.single (g,w) 1)):=by
  induction w generalizing g with
  | nil=>simp
  | cons x w ih=>
    obtain ⟨hx,hw⟩:=List.pairwise_cons.mp hw
    have ha:g*(v x)⁻¹*(w.map (fun a=>(v a)⁻¹)).prod*v x =
        g*(w.map (fun a=>(v a)⁻¹)).prod:=by
      have hh:=(NV (fun a=>(v a)⁻¹) x w (fun y hy=>(hx y hy).inv_left.inv_right)).inv_left.eq
      simp only [inv_inv] at hh
      rw [mul_assoc,← hh]
      group
    rw [dK,map_sub,map_sub,Ep,← Nv _ _ _ _ (fun y hy=>(hx y hy).inv_left.inv_right),ih _ hw]
    simp only [nT,one_smul,map_smul,gI,dK,
      List.length_cons,pow_succ,List.map_cons,List.prod_cons,← mul_assoc,ha,
      mul_neg,mul_one,neg_smul,map_neg,smul_sub]
    abel
theorem Sz (g:G) (w:List A)
    (hw:w.Pairwise (fun a b=>Commute (v a) (v b))) :
    mirror (fun a=>(v a)⁻¹) (mirror v (Finsupp.single (g,w) 1))=Finsupp.single (g,w) 1:=by
  rw [nT v g w 1,one_smul,map_smul,
    nT _ _ w 1,one_smul,
    prod_inv v w hw,smul_smul,<- mul_pow]
  simp
open HeightFiltration
variable [LinearOrder A] (L:SimpleGraph A)
variable (comm:∀ a b,L.Adj a b -> Commute (v a) (v b))
private theorem rG {S T:Set (G × List A)}
  (step:∀ g w,(g,w) ∈ S → (g*(w.map (fun a=>(v a)⁻¹)).prod,w) ∈ T)
  {c:Chains G A} (hc:c ∈ Finsupp.supported ℤ ℤ S):mirror v c ∈ Finsupp.supported ℤ ℤ T:=by
 apply d8 _ _ _ _ hc
 rintro ⟨g,w⟩ hp
 rw [nT,one_smul]
 exact Submodule.smul_mem _ _ (Finsupp.single_mem_supported ℤ 1 (step g w hp))
theorem NW {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
  mirror v c ∈ total (G:=G) L k:=rG v (fun _ _ hp=>hp) hc
include comm in
private theorem DK (f g:Chains G A →ₗ[ℤ] Chains G A)
  (hs:∀ x w,w.Pairwise (fun a b=>Commute (v a) (v b)) →
   f (Finsupp.single (x,w) 1)=g (Finsupp.single (x,w) 1))
  {k c} (hc:c ∈ total (G:=G) L k):f c=g c:=by
 rw [total,Finsupp.supported_eq_span_single] at hc
 apply LinearMap.eqOn_span (f:=f) (g:=g) _ hc
 rintro _ ⟨⟨x,w⟩,⟨hw,_⟩,rfl⟩
 exact hs x w (hw.2.imp (fun ha=>comm _ _ ha))
include comm in
theorem v3 {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
  mirror v (boundary v⁻¹ c)=boundary v (mirror v c):=by
 apply DK v L comm ((mirror v).comp (boundary v⁻¹)) ((boundary v).comp (mirror v)) _ hc
 intro x w hw
 simpa only [LinearMap.comp_apply,gI,one_smul,Pi.inv_def] using z8 v x w hw
include comm in
theorem NY {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
  mirror v⁻¹ (mirror v c)=c:=by
 exact DK v L comm ((mirror v⁻¹).comp (mirror v)) LinearMap.id (Sz v) hc
include comm in
private theorem Br:∀ a b,L.Adj a b → Commute ((v⁻¹) a) ((v⁻¹) b):=
 fun a b ha=>(comm a b ha).inv_left.inv_right
include comm in
private theorem CJ {k j} {c:Chains G A} (hc:c ∈ total L k) (hz:boundary v⁻¹ c=0)
  {S T:Submodule ℤ (Chains G A)} (ht:T ≤ total L j) (back:∀ b ∈ T,mirror v⁻¹ b ∈ S)
  (fill:boundary v (mirror v c)=0 → ∃ b ∈ T,boundary v b=mirror v c) :
  ∃ b ∈ S,boundary v⁻¹ b=c:=by
 obtain ⟨b,hb,he⟩:=fill (by rw [← v3 v L comm hc,hz,map_zero])
 refine ⟨_,back b hb,?_⟩
 have eq:=v3 v⁻¹ L (Br v L comm) (ht hb)
 rw [inv_inv,he,NY v L comm hc] at eq
 exact eq.symm
include comm in
theorem SD
  (exactTotal:∀ {k:ℕ},0 < k -> ∀ c,c ∈ total (G:=G) L k -> boundary v c=0 ->
   ∃ b ∈ total (G:=G) L (k+1),boundary v b=c)
  {k:ℕ} (hk:0 < k) (c:Chains G A) (hc:c ∈ total (G:=G) L k)
  (hz:boundary (fun a=>(v a)⁻¹) c=0) :
  ∃ b ∈ total (G:=G) L (k+1),boundary (fun a=>(v a)⁻¹) b=c:=by
 exact CJ v L comm hc hz le_rfl (fun _=>NW _ L) (exactTotal hk _ (NW v L hc))
variable (h:G -> ℤ)
variable (hv:∀ g a,h (g * v a)=h g + 1)
omit [LinearOrder A] in
include hv in
private theorem Aw (g:G) (a:A): -h (g*(v⁻¹) a) = -h g+1:=by
 change -h (g*(v a)⁻¹) = _
 have he:=hv (g*(v a)⁻¹) a
 rw [inv_mul_cancel_right] at he
 omega
omit [LinearOrder A] in
include hv in
theorem BZ (g:G) (w:List A):h (g*(w.map v).prod)=h g + w.length:=by
 induction w generalizing g with
 | nil=>simp
 | cons a w ih=>
  simp only [List.map_cons,List.prod_cons,<- mul_assoc,ih,hv,List.length_cons,Nat.cast_add,Nat.cast_one]
  omega

def below (k:ℕ):Submodule ℤ (Chains G A):=
 Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 /\ p.2.length=k /\ h p.1 + k <= 0}
omit [Group G] in
theorem Lg {k:ℕ} {c:Chains G A} (hc:c ∈ below L h k) :
  c ∈ total (G:=G) L k:=by
 apply Finsupp.supported_mono _ hc
 intro p hp
 exact ⟨hp.1,hp.2.1⟩
include comm hv in
theorem tA {k:ℕ} {c:Chains G A}
  (hc:c ∈ above L (fun g=>-h g) k 0):mirror v c ∈ below L h k:=by
 apply rG v _ hc
 rintro g w ⟨hw,hl,hh⟩
 refine ⟨hw,hl,?_⟩
 dsimp at hw hl hh
 have ht:=BZ v⁻¹ (fun g=>-h g) (Aw v h hv) g w
 change h (g*(w.map v⁻¹).prod)+(k:ℤ) ≤ 0
 rw [hl] at ht
 omega
include hv in
theorem tB {k:ℕ} {c:Chains G A} (hc:c ∈ below L h k) :
  mirror v⁻¹ c ∈ above L (fun g=>-h g) k 0:=by
 apply rG v⁻¹ _ hc
 rintro g w ⟨hw,hl,hh⟩
 dsimp at hw hl hh ⊢
 refine ⟨hw,hl,?_⟩
 simp only [inv_inv]
 change 0 <= -h (g*(w.map v).prod)
 rw [BZ v h hv,hl]
 omega
include comm hv in
theorem xT {k:ℕ} {c:Chains G A} (hc:c ∈ below L h k) :
  boundary v c ∈ below L h (k-1):=by
 have hm:=tB v L h hv hc
 have hd:=tA v L comm h hv (m5 L v⁻¹ _ (Aw v h hv) hm)
 rw [v3 v L comm (Jh L _ hm)] at hd
 have hi:=NY v⁻¹ L (Br v L comm) (Lg L h hc)
 rw [inv_inv] at hi
 rwa [hi] at hd
variable (K:SimplicialChains.Contraction L)
include comm hv K in
theorem Az
  (exactTotal:∀ {k:ℕ},0 < k -> ∀ c,c ∈ total (G:=G) L k -> boundary v c=0 ->
   ∃ b ∈ total (G:=G) L (k+1),boundary v b=c)
  {k:ℕ} (hk:0 < k) (c:Chains G A) (hc:c ∈ below L h k)
  (hz:boundary v c=0) :
  ∃ b ∈ below L h (k+1),boundary v b=c:=by
 have fill:=o9 L K v⁻¹ _ (Aw v h hv) (Br v L comm)
  (fun hk c hc hz=>SD v L comm exactTotal hk c hc hz) hk _ (tB v L h hv hc)
 simpa only [inv_inv] using CJ v⁻¹ L (Br v L comm) (Lg L h hc) (by simpa only [inv_inv] using hz)
  (fun _ hb=>Jh L _ hb) (fun b hb=>by simpa only [inv_inv] using tA v L comm h hv hb) fill
end CubicalChains.Reflection
namespace CubicalChains.LevelExact
open HeightFiltration Reflection
variable {G A:Type*} [Group G] [LinearOrder A] (L:SimpleGraph A)
variable (v:A -> G) (h:G -> ℤ)
def nU (P:G × List A -> Prop) [DecidablePred P]:Chains G A →ₗ[ℤ] Chains G A where
 toFun:=Finsupp.filter P
 map_add' _ _:=Finsupp.filter_add
 map_smul' _ _:=Finsupp.filter_smul
omit [Group G] [LinearOrder A] in
@[simp] theorem N4 (P:G × List A -> Prop) [DecidablePred P] (p:G × List A) (n:ℤ) :
  nU P (Finsupp.single p n)=if P p then Finsupp.single p n else 0:=by
 split <;> first | apply Finsupp.filter_single_of_pos _ (by assumption) | apply Finsupp.filter_single_of_neg _ (by assumption)
omit [Group G] [LinearOrder A] in
private theorem wN (P:G × List A -> Prop) [DecidablePred P] {Q:Set (G × List A)}
  {c:Chains G A} (hc:c ∈ Finsupp.supported ℤ ℤ Q) :
  nU P c ∈ Finsupp.supported ℤ ℤ {p | p ∈ Q /\ P p}:=by
 apply (Finsupp.mem_supported _ _).2
 intro p hp
 obtain ⟨hp,hP⟩:=Finset.mem_filter.mp hp
 exact ⟨(Finsupp.mem_supported _ _).1 hc hp,hP⟩
def plus:Chains G A →ₗ[ℤ] Chains G A:=nU (fun p=>0 <= h p.1)
def iQ:Chains G A →ₗ[ℤ] Chains G A:=nU (fun p=>h p.1 < 0 /\ 0 < h p.1+p.2.length)
def crossing (k:ℕ):Submodule ℤ (Chains G A):=
  Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 /\ p.2.length=k /\
    h p.1 < 0 /\ 0 < h p.1+k}
omit [Group G] in
theorem Kw {k:ℕ} {c:Chains G A} (hc:c ∈ crossing L h k) :
  c ∈ total (G:=G) L k:=by
 apply Finsupp.supported_mono _ hc
 intro p hp
 exact ⟨hp.1,hp.2.1⟩
omit [Group G] in
theorem N5 {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
  plus h c ∈ above L h k 0:=by
 apply Finsupp.supported_mono _ (wN (fun p=>0 <= h p.1) hc)
 intro p hp
 exact ⟨hp.1.1,hp.1.2,hp.2⟩
omit [Group G] in
theorem Lh {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
  iQ h c ∈ crossing L h k:=by
 apply Finsupp.supported_mono _
  (wN (fun p=>h p.1<0 /\ 0<h p.1+p.2.length) hc)
 intro p hp
 exact ⟨hp.1.1,hp.1.2,hp.2.1,by simpa only [hp.1.2] using hp.2.2⟩
omit [Group G] in
private theorem B8 {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
    ∃ b ∈ below L h k,c=plus h c + b + iQ h c:=by
  refine ⟨c-plus h c-iQ h c,?_,by abel⟩
  apply (Finsupp.mem_supported' _ _).2
  intro p hp
  simp only [Finsupp.sub_apply,plus,iQ,nU,LinearMap.coe_mk,AddHom.coe_mk,
    Finsupp.filter_apply]
  by_cases hz:c p=0
  · simp [hz]
  obtain ⟨hw,hl⟩:=(Finsupp.mem_supported _ _).1 hc (Finsupp.mem_support_iff.mpr hz)
  have hh:¬ h p.1+k ≤ 0:=fun hh=>hp ⟨hw,hl,hh⟩
  split_ifs <;> omega
omit [Group G] in
theorem N6 {k:ℕ} {c:Chains G A} (hc:c ∈ above L h k 0) :
  iQ h c=0:=by
 apply (Finsupp.filter_eq_zero_iff _ _).2
 exact fun p hp=>(Finsupp.mem_supported' ℤ c).1 hc p (fun hh=> (not_lt.mpr hh.2.2) hp.1)
omit [Group G] in
theorem qL {k:ℕ} {c:Chains G A} (hc:c ∈ below L h k) :
  iQ h c=0:=by
 apply (Finsupp.filter_eq_zero_iff _ _).2
 exact fun p hp=>(Finsupp.mem_supported' ℤ c).1 hc p (fun ⟨_,hl,hh⟩=>by have:=hp.2; omega)
omit [Group G] in
theorem SH {k:ℕ} {c:Chains G A} (hc:c ∈ crossing L h k):iQ h c=c:=by
 apply (Finsupp.filter_eq_self_iff _ _).2
 intro p hn
 obtain ⟨_,hl,ha,hb⟩:=(Finsupp.mem_supported ℤ c).1 hc (Finsupp.mem_support_iff.mpr hn)
 exact ⟨ha,by simpa only [hl] using hb⟩
omit [Group G] in
theorem BG {c:Chains G A} (hc:c ∈ crossing L h 1):c=0:=by
 apply Finsupp.ext
 intro p
 by_contra hn
 have hp:=(Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
 have h₁:=hp.2.2.1
 have h₂:=hp.2.2.2
 omega
omit [Group G] in
theorem BH {k:ℕ} (hk:0 < k) {c:Chains G A}
  (hc:c ∈ above L h k 0) (hd:c ∈ below L h k):c=0:=by
 apply Finsupp.ext
 intro p
 by_contra hn
 have hp:=(Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
 have hq:=(Finsupp.mem_supported ℤ c).mp hd (Finsupp.mem_support_iff.mpr hn)
 have h₁:=hp.2.2
 have h₂:=hq.2.2
 omega
variable (K:SimplicialChains.Contraction L)
variable (hv:∀ g a,h (g * v a)=h g + 1)
variable (comm:∀ a b,L.Adj a b -> Commute (v a) (v b))
variable (exactTotal:∀ {k:ℕ},0 < k -> ∀ c,c ∈ total (G:=G) L k -> boundary v c=0 ->
   ∃ b ∈ total (G:=G) L (k+1),boundary v b=c)
include hv in
theorem Lj {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
  boundary v c ∈ total (G:=G) L (k-1):=by
 obtain ⟨N,hN⟩:=oI L h hc
 exact Jh L h (m5 L v h hv hN)
include comm in
theorem v9 (h:G -> ℤ) {k:ℕ} {c:Chains G A} (hc:c ∈ total (G:=G) L k) :
  boundary v (boundary v c)=0:=by
 obtain ⟨N,hN⟩:=oI L h hc
 exact r6 L v h comm hN
def f8:Chains G A →ₗ[ℤ] Chains G A:=
 (boundary v).comp ((plus h).comp (boundary v))
omit [LinearOrder A] in
theorem s5 (c:Chains G A) :
  f8 v h c=boundary v (plus h (boundary v c)):=rfl
include hv comm K exactTotal in
private theorem DM {k:ℕ} (hk:2 ≤ k) (c:Chains G A) (hc:c ∈ crossing L h k)
    (hz:iQ h (boundary v c)=0) (obstruction:k=2 -> f8 v h c=0) :
    ∃ t ∈ crossing L h (k+1),iQ h (boundary v t)=c:=by
  have ht:=Kw L h hc
  have hd:=Lj L v h hv ht
  have hp:=N5 L h hd
  obtain ⟨m,hm,he⟩:=B8 L h hd
  rw [hz,add_zero] at he
  have hh:=congrArg (boundary v) he
  rw [v9 L v comm h ht,map_add] at hh
  have hdp:boundary v (plus h (boundary v c))=0:=by
    by_cases h₂:k=2
    · exact obstruction h₂
    apply BH L h (by omega) (m5 L v h hv hp)
    rw [eq_neg_of_add_eq_zero_left hh.symm]
    exact Submodule.neg_mem _ (xT v L comm h hv hm)
  rw [hdp,zero_add] at hh
  obtain ⟨a,ha,hda⟩:=o9 L K v h hv comm exactTotal (by omega) _ hp hdp
  obtain ⟨b,hb,hdb⟩:=Az v L comm h hv K exactTotal (by omega) _ hm hh.symm
  rw [show k-1+1=k by omega] at ha hb
  have hab:c-a-b ∈ total (G:=G) L k:=Submodule.sub_mem _
    (Submodule.sub_mem _ ht (Jh L h ha)) (Lg L h hb)
  have hdz:boundary v (c-a-b)=0:=by
    simp only [map_sub,hda,hdb]
    exact sub_eq_zero.mpr (sub_eq_iff_eq_add.mpr (he.trans (add_comm _ _)))
  obtain ⟨t,ht',hdt⟩:=exactTotal (by omega) _ hab hdz
  refine ⟨iQ h t,Lh L h ht',?_⟩
  obtain ⟨m',hm',he'⟩:=B8 L h ht'
  have hh':=congrArg (fun z=>iQ h (boundary v z)) he'
  simp only [map_add,N6 L h (m5 L v h hv (N5 L h ht')),
    qL L h (xT v L comm h hv hm'),zero_add] at hh'
  rw [← hh',hdt,map_sub,map_sub,SH L h hc,N6 L h ha,qL L h hb,sub_zero,sub_zero]
include hv comm K exactTotal in
theorem SI (c:Chains G A) (hc:c ∈ crossing L h 2)
  (hz:f8 v h c=0) :
  ∃ t ∈ crossing L h 3,iQ h (boundary v t)=c:=by
 exact DM L v h K hv comm exactTotal (by decide) c hc
  (BG L h (Lh L h (Lj L v h hv (Kw L h hc)))) (fun _=>hz)
variable (dim:∀ w,SimplicialChains.Valid L w -> w.length <= 3)
include dim in
omit [Group G] in
theorem CQ {c:Chains G A} (hc:c ∈ total (G:=G) L 4):c=0:=by
 apply Finsupp.ext
 intro p
 by_contra hn
 have hp:=(Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr hn)
 have hh:=dim p.2 hp.1
 have hl:=hp.2
 omega
include hv comm K exactTotal dim in
theorem SK (t:Chains G A) (ht:t ∈ crossing L h 3)
  (hz:iQ h (boundary v t)=0):t=0:=by
 obtain ⟨q,hq,hb⟩:=DM L v h K hv comm exactTotal (by decide) t ht hz (by omega)
 simpa [CQ L dim (Kw L h hq)] using hb.symm
end CubicalChains.LevelExact
end
noncomputable section
open Classical Set Topology
namespace EilenbergGanea
abbrev SourceGroup:=(height seedGraph).ker
def cohomologicalDimension (G:Type*) [Group G]:WithBot ℕ∞:=
 CategoryTheory.projectiveDimension
  (ModuleCat.of (MonoidAlgebra ℤ G) (Representation.trivial ℤ G ℤ).asModule)
universe u
def HasClassifyingSpace (G:Type*) [Group G] (n:ℕ):Prop:=
 ∃ (X:Type u) (_:TopologicalSpace X) (_:T2Space X)
  (_:Topology.CWComplex (Set.univ:Set X)),
  (∀ k:ℕ,n < k -> IsEmpty (Topology.CWComplex.cell (Set.univ:Set X) k)) /\
  PathConnectedSpace X /\
  ∃ x:X,Nonempty (FundamentalGroup X x ≃* G) /\
  ∃ (E:Type u) (_:TopologicalSpace E),ContractibleSpace E /\
  ∃ p:E -> X,IsCoveringMap p /\ Function.Surjective p
end EilenbergGanea
namespace EilenbergGanea
theorem source_residuallyFinite:Group.ResiduallyFinite SourceGroup:=by
 have:=wS SeedCell seedGraph
 infer_instance
end EilenbergGanea
end
noncomputable section
open Set Filter Topology
namespace EilenbergGanea
section FixedRegularization
variable {A V:Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
 [NormedAddCommGroup V] [NormedSpace ℝ V]
def r2 (f:A × V -> A × V) (a:A):A:=(f (a,0)).1
end FixedRegularization
end EilenbergGanea
open Set Filter Topology
open scoped ContDiff
open Set Filter Topology
namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
section CompactRootStability
variable {P X Y:Type*} [TopologicalSpace P] [TopologicalSpace X]
 [TopologicalSpace Y] [CompactSpace X] [T1Space Y]
theorem SM (f:P × X -> Y) (hf:Continuous f)
  (y:Y) (V:Set (P × X)) (hV:IsOpen V) (p₀:P)
  (h₀:∀ x,f (p₀,x)=y -> (p₀,x) ∈ V) :
  ∀ᶠ p in 𝓝 p₀,∀ x,f (p,x)=y -> (p,x) ∈ V:=by
 let C:Set (P × X):={q | f q=y} ∩ Vᶜ
 have hC:IsClosed C:=(isClosed_singleton.preimage hf).inter hV.isClosed_compl
 have hn:p₀ ∉ Prod.fst '' C:=by
  rintro ⟨⟨p,x⟩,⟨hr,hv⟩,rfl⟩
  exact hv (h₀ x hr)
 filter_upwards [(isClosedMap_fst_of_compactSpace _ hC).isOpen_compl.mem_nhds hn] with p hp
 intro x hr
 by_contra hv
 exact hp ⟨(p,x),⟨hr,hv⟩,rfl⟩
end CompactRootStability
end EilenbergGanea
end
noncomputable section
open Set Filter Topology
open scoped Quaternion ContDiff
open scoped Quaternion
namespace EilenbergGanea
abbrev a3:=unitary ℍ
theorem c9 (q:ℍ):q ∈ unitary ℍ ↔ ‖q‖=1:=by
 rw [Unitary.mem_iff,Quaternion.star_mul_self,Quaternion.self_mul_star,and_self]
 constructor
 ·intro h
  have he:Quaternion.normSq q=1:=Quaternion.coe_inj.mp h
  rw [Quaternion.normSq_eq_norm_mul_self] at he
  nlinarith [norm_nonneg q]
 ·intro h
  simp [Quaternion.normSq_eq_norm_mul_self,h]
instance JR:CompactSpace a3:=by
 apply isCompact_iff_compactSpace.mp
 have hs:(unitary ℍ:Set ℍ)=Metric.sphere 0 1:=by
  ext q
  simp [c9]
 rw [hs]
 exact isCompact_sphere 0 1
def vV:Circle →* a3 where
 toFun z:=⟨Quaternion.ofComplex z,by
  rw [Unitary.mem_iff,Quaternion.star_mul_self,Quaternion.self_mul_star,and_self]
  have hz:=Circle.normSq_coe z
  have he:Quaternion.normSq (Quaternion.ofComplex z)=1:=by
   simpa [Quaternion.normSq_def',Complex.normSq_apply,sq] using hz
  rw [he]; rfl⟩
 map_one':=Subtype.ext (map_one Quaternion.ofComplex)
 map_mul' z w:=Subtype.ext (map_mul Quaternion.ofComplex (z:ℂ) (w:ℂ))
def c8 {m:ℕ} (w:Fin m -> FreeGroup (Fin m)):Matrix (Fin m) (Fin m) ℤ:=
 fun i j=>Multiplicative.toAdd
  (FreeGroup.lift (fun k=>Multiplicative.ofAdd (if j=k then (1:ℤ) else 0)) (w i))
open Set Filter Topology
open scoped ContDiff
def bT (q:ℍ):a3:=by
 classical
 exact if h:q=0 then 1 else
  ⟨‖q‖⁻¹ • q,(c9 _).mpr (by
   simp only [norm_smul,Real.norm_eq_abs,abs_inv,abs_norm]
   exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h))⟩
theorem c1 {q:ℍ} (hq:q ≠ 0) :
  (bT q:ℍ)=‖q‖⁻¹ • q:=by simp [bT,hq]
theorem g5 {q:ℍ} (hq:q ≠ 0) :
  ContDiffAt ℝ ∞ (fun z=>(bT z:ℍ)) q:=by
 have h:ContDiffAt ℝ ∞ (fun z:ℍ=>‖z‖⁻¹ • z) q:=
  ((contDiffAt_norm ℝ hq).inv (norm_ne_zero_iff.mpr hq)).smul contDiffAt_id
 apply h.congr_of_eventuallyEq
 filter_upwards [eventually_ne_nhds hq] with z hz
 exact c1 hz
theorem SO {q:ℍ} (hq:q ≠ 0) :
  ContinuousAt bT q:=by
 exact tendsto_subtype_rng.mpr (g5 hq).continuousAt
@[simp] theorem SX (q:a3):bT (q:ℍ)=q:=by
 have hqnorm:‖(q:ℍ)‖=1:=(c9 _).mp q.property
 have hq:(q:ℍ) ≠ 0:=by intro he; simp [he] at hqnorm
 apply Subtype.ext
 simp [c1 hq,hqnorm]
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
variable {n:Type*} [Fintype n] [DecidableEq n]
def i9 (x:n -> ℂ):(n -> ℂ) →L[ℝ] (n -> ℂ):=
 ((Matrix.diagonal x).toLin').toContinuousLinearMap.restrictScalars ℝ
@[simp] theorem SY (x z:n -> ℂ) (i:n) :
  i9 x z i=x i * z i:=by simp [i9,Matrix.toLin'_apply,Matrix.mulVec,Matrix.diagonal_apply,dotProduct]
end EilenbergGanea
namespace EilenbergGanea
section CommutativeWords
variable {n A:Type*} [Fintype n] [DecidableEq n] [CommGroup A]
def dN {ι:Type*} [DecidableEq ι] (w:FreeGroup ι) (j:ι):ℤ:=
 Multiplicative.toAdd
  (FreeGroup.lift (fun k=>Multiplicative.ofAdd (if j=k then (1:ℤ) else 0)) w)
@[simp] theorem dq8 {ι:Type*} [DecidableEq ι] (j:ι):dN (1:FreeGroup ι) j=0:=by
 simp [dN]
@[simp] theorem dr9 {ι:Type*} [DecidableEq ι] (j k:ι) :
  dN (FreeGroup.of k) j=if j=k then 1 else 0:=by
 simp [dN]
@[simp] theorem dr2 {ι:Type*} [DecidableEq ι] (w:FreeGroup ι) (j:ι) :
  dN w⁻¹ j=-dN w j:=by
 simp [dN]
@[simp] theorem dr1 {ι:Type*} [DecidableEq ι] (w v:FreeGroup ι) (j:ι) :
  dN (w * v) j=dN w j + dN v j:=by
 simp [dN]
end CommutativeWords
open Set Filter Topology
open scoped Quaternion ContDiff
def bZ:ℍ ≃ₗ[ℝ] ℂ × ℂ where
 toFun q:=(⟨q.re,q.imI⟩,⟨q.imJ,q.imK⟩)
 invFun z:=⟨z.1.re,z.1.im,z.2.re,z.2.im⟩
 left_inv q:=by cases q; rfl
 right_inv z:=by rcases z with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
 map_add' q r:=by ext <;> rfl
 map_smul' r q:=by apply Prod.ext <;> apply Complex.ext <;> simp
@[simp] theorem SZ (q:ℍ) :
  bZ q=(⟨q.re,q.imI⟩,⟨q.imJ,q.imK⟩):=rfl
@[simp] theorem i1 (z:ℂ) :
  bZ (Quaternion.ofComplex z)=(z,0):=by
 ext <;> rfl
@[simp] theorem k9 (z:ℂ):‖Quaternion.ofComplex z‖=‖z‖:=by
 have h:‖Quaternion.ofComplex z‖ ^ 2=‖z‖ ^ 2:=by
  rw [sq,<- Quaternion.normSq_eq_norm_mul_self,<- Complex.normSq_eq_norm_sq]
  simp [Quaternion.normSq_def',Complex.normSq_apply,sq]
 nlinarith [norm_nonneg (Quaternion.ofComplex z),norm_nonneg z]
def aP {m:ℕ} :
    (Fin m -> ℍ) ≃L[ℝ] ((Fin m -> ℂ) × (Fin m -> ℂ)):=
  (show (Fin m -> ℍ) ≃ₗ[ℝ] ((Fin m -> ℂ) × (Fin m -> ℂ)) from
    { toFun:=fun q=>(fun i=>(bZ (q i)).1,
        fun i=>(bZ (q i)).2)
      invFun:=fun z i=>bZ.symm (z.1 i,z.2 i)
      left_inv:=by intro q; funext i; exact bZ.symm_apply_apply _
      right_inv:=by intro z; ext i <;> simp
      map_add':=by intro q r; ext i <;> rfl
      map_smul':=by intro r q; ext i <;> simp [bZ] }).toContinuousLinearEquiv
@[simp] theorem h9 {m:ℕ} (z:Fin m -> ℂ) :
    aP (fun i=>Quaternion.ofComplex (z i))=(z,0):=by
  apply Prod.ext
  · funext i; exact congrArg Prod.fst (i1 (z i))
  · funext i; exact congrArg Prod.snd (i1 (z i))
@[simp] theorem n7 {m:ℕ} (z:Fin m -> ℂ) :
  aP.symm (z,0)=fun i=>Quaternion.ofComplex (z i):=by
 exact aP.injective (by rw [ContinuousLinearEquiv.apply_symm_apply,h9])
theorem S5 (c:ℂ) (q:ℍ) :
  bZ (Quaternion.ofComplex c * q * star (Quaternion.ofComplex c)) =
   ((Complex.normSq c:ℂ) * (bZ q).1,
    c ^ 2 * (bZ q).2):=by
 apply Prod.ext <;> apply Complex.ext <;>
  simp [SZ,Complex.normSq_apply,pow_two] <;> ring
@[simp] theorem r3 (c:Circle) (q:ℍ) :
  bZ (Quaternion.ofComplex c * q * star (Quaternion.ofComplex c)) =
   ((bZ q).1,(c:ℂ) ^ 2 * (bZ q).2):=by
 simpa using S5 (c:ℂ) q
def aY (a:a3) (q:ℍ):ℍ:=(a:ℍ) * q * star (a:ℍ)
@[simp] theorem h7 (a:a3) (q:ℍ) :
  ‖aY a q‖=‖q‖:=by
 have ha:=(c9 _).mp a.property
 simp [aY,ha]
@[simp] theorem dh0 (a:a3):aY a 0=0:=by
 simp [aY]
@[simp] theorem bo7 (a:a3):aY a 1=1:=by
 simp [aY]
end EilenbergGanea
namespace EilenbergGanea
theorem S6 (z:ℂ) (hz:‖z‖=1) :
  ∃ c:Circle,(c:ℂ) ^ 2=z:=by
 obtain ⟨c,hc⟩:=IsAlgClosed.exists_pow_nat_eq z (by decide:0 < 2)
 have hn:‖c‖=1:=by
  have hh:=congrArg norm hc
  rw [norm_pow,hz] at hh
  nlinarith [norm_nonneg c]
 exact ⟨⟨c,mem_sphere_zero_iff_norm.mpr hn⟩,hc⟩
open Set Filter Topology
open scoped Quaternion ContDiff
theorem i5 {m:ℕ} (c:Circle) (q:Fin m -> ℍ) :
    aP (fun i=>aY (vV c) (q i)) =
      ((aP q).1,(c:ℂ) ^ 2 • (aP q).2):=by
  apply Prod.ext
  · funext i
    change (bZ (Quaternion.ofComplex c * q i * star (Quaternion.ofComplex c))).1=_
    have hh:=congrArg Prod.fst (r3 c (q i))
    exact hh
  · funext i
    change (bZ (Quaternion.ofComplex c * q i * star (Quaternion.ofComplex c))).2=_
    have hh:=congrArg Prod.snd (r3 c (q i))
    exact hh
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped ContDiff
private abbrev nZ (m:ℕ):=Fin m → ℂ
private abbrev Pair (m:ℕ):=nZ m × nZ m
variable {m:ℕ}
private def weight (z:ℂ):ℝ:=Complex.normSq z
private def term (z:ℂ) (p:Pair m):Pair m:=(weight z • p.1,weight z • z • p.2)
private def lU (f:Pair m → Pair m) (x:Pair m) (p:OrbitSlice.Params m):=f x + ∑ j,term (x.2 j) (p j)
private theorem xW (f:Pair m → Pair m) (hf:ContDiff ℝ ∞ f) :
  ContDiff ℝ ∞ (fun q:OrbitSlice.Params m × Pair m=>lU f q.2 q.1):=by
 simp only [lU,term,weight,Complex.normSq_apply,← Complex.reCLM_apply,← Complex.imCLM_apply]; fun_prop
private theorem Er (f:Pair m → Pair m) (hf:ContDiff ℝ ∞ f) (p:OrbitSlice.Params m) (a:nZ m) :
  fderiv ℝ (fun x=>lU f x p) (a,0) = fderiv ℝ f (a,0):=by
 have H (j:Fin m):HasFDerivAt (𝕜:=ℝ) (fun x:Pair m=>term (x.2 j) (p j)) 0 (a,0):=by
  let l:=(ContinuousLinearMap.proj (R:=ℝ) (φ:=fun _:Fin m=>ℂ) j).comp (ContinuousLinearMap.snd ℝ (nZ m) (nZ m))
  have hr:=(Complex.reCLM.comp l).hasFDerivAt (x:=(a,0))
  have hi:=(Complex.imCLM.comp l).hasFDerivAt (x:=(a,0))
  have hn:HasFDerivAt (𝕜:=ℝ) (fun x:Pair m=>weight (x.2 j)) 0 (a,0):=by
   have hh:=(hr.mul hr).add (hi.mul hi)
   simp [l] at hh
   exact hh
  have hh:=(hn.smul (hasFDerivAt_const (p j).1 (a,0))).prodMk (hn.smul (l.hasFDerivAt.smul (hasFDerivAt_const (p j).2 (a,0))))
  have w0:weight 0 = 0:=by simp [weight]
  simp [w0,l] at hh
  rw [show (0:Pair m →L[ℝ] Pair m) = ContinuousLinearMap.prod 0 0 by ext <;> simp]; exact hh
 have hh:=((hf.differentiable (by simp) (a,0)).hasFDerivAt.add (HasFDerivAt.fun_sum (u:=Finset.univ) (fun j _=>H j))).fderiv
 rw [show (fun x=>lU f x p) = f + fun y=>∑ i,term (y.2 i) (p i) from rfl]; simpa using hh
private def vF (f:Pair m → Pair m) (i:Fin m) (q:OrbitSlice.Params m):=
 f (q i) + ∑ j ∈ Finset.univ.erase i,term ((q i).2 j) (q j)
private def chart (f:Pair m → Pair m) (i:Fin m) (q:OrbitSlice.Params m):=
 let z:=(q i).2 i
 let r:=vF f i q
 Function.update q i ((weight z)⁻¹ • -r.1,(weight z)⁻¹ • z⁻¹ • -r.2)
private theorem H7 (f:Pair m → Pair m) (hf:ContDiff ℝ ∞ f) (i:Fin m) (q:OrbitSlice.Params m) (hz:(q i).2 i ≠ 0):DifferentiableAt ℝ (chart f i) q:=by
 have hw:weight ((q i).2 i) ≠ 0:=by simpa [weight] using hz
 apply differentiableAt_pi.mpr; intro j; by_cases h:j=i
 ·subst j; simp only [chart,Function.update_self]
  have hr:DifferentiableAt ℝ (vF f i) q:=by
   have:=hf.differentiable (by simp)
   unfold vF; simp only [term,weight,Complex.normSq_apply,← Complex.reCLM_apply,← Complex.imCLM_apply]; fun_prop
  have w:DifferentiableAt ℝ (fun q:OrbitSlice.Params m=>weight ((q i).2 i)) q:=by
   simp only [weight,Complex.normSq_apply,← Complex.reCLM_apply,← Complex.imCLM_apply]; fun_prop
  have z:DifferentiableAt ℝ (fun q:OrbitSlice.Params m=>(q i).2 i) q:=by fun_prop
  exact ((w.inv hw).smul hr.fst.neg).prodMk ((w.inv hw).smul ((z.inv hz).smul hr.snd.neg))
 ·simpa only [chart,Function.update_of_ne h] using differentiableAt_apply j q (𝕜:=ℝ)
private theorem Ie (f:Pair m → Pair m) (i:Fin m) (x:Pair m) (p:OrbitSlice.Params m) (hz:x.2 i ≠ 0) (h:lU f x p = 0):chart f i (Function.update p i x) = p:=by
 have he:vF f i (Function.update p i x) = f x + ∑ j ∈ Finset.univ.erase i,term (x.2 j) (p j):=by
  simp only [vF,Function.update_self]; congr 1; apply Finset.sum_congr rfl
  intro j hj; rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
 rw [lU,← Finset.sum_erase_add _ _ (Finset.mem_univ i),← add_assoc,← he] at h
 have hh:=eq_neg_of_add_eq_zero_right h
 have hw:weight (x.2 i) ≠ 0:=by simpa [weight] using hz
 funext j; by_cases hj:j=i
 ·subst j; simp only [chart,Function.update_self,← Prod.fst_neg,← Prod.snd_neg,← hh,term,inv_smul_smul₀ hw]
  rw [smul_comm ((x.2 i)⁻¹) (weight (x.2 i)),inv_smul_smul₀ hw,inv_smul_smul₀ hz]
 ·simp [chart,Function.update_of_ne hj]
private theorem D6 (f:Pair m → Pair m) (hf:ContDiff ℝ ∞ f)
  (K:Set (Pair m)) (hK:IsCompact K) (ε:ℝ) (hε:0 < ε)
  : ∀ᶠ p:OrbitSlice.Params m in 𝓝 0,∀ x:K,‖lU f x.val p - f x.val‖ < ε:=by
 let:CompactSpace K:=isCompact_iff_compactSpace.mp hK
 have hc:Continuous (fun q:OrbitSlice.Params m × K=>(q.1,q.2.val)):=
  continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
 have hopen:IsOpen {q:OrbitSlice.Params m × K | ‖lU f q.2.val q.1 - f q.2.val‖ < ε}:=
  isOpen_lt (((xW f hf).continuous.comp hc).sub
   (hf.continuous.comp (continuous_subtype_val.comp continuous_snd))).norm continuous_const
 have h:=SM (fun _:OrbitSlice.Params m × K=>(0:ℝ)) continuous_const (0:ℝ) _ hopen 0 (by
   intro x _
   simpa [lU,term] using hε)
 filter_upwards [h] with p hp
 exact fun x=>hp x rfl
open MeasureTheory in
private theorem Fp (f:Pair m → Pair m) (hf:ContDiff ℝ ∞ f)
  (rot:∀ (c:ℂ) (_:‖c‖ = 1) x,f (x.1,c • x.2) = ((f x).1,c • (f x).2))
  (U:Set (OrbitSlice.Params m)) (hU:U ∈ 𝓝 0) :
  ∃ p ∈ U,∀ x,lU f x p = 0 → x.2 = 0:=by
 classical
 let:MeasurableSpace (OrbitSlice.Params m):=borel _
 let:BorelSpace (OrbitSlice.Params m):=⟨rfl⟩
 let μ:=(Module.finBasis ℝ (OrbitSlice.Params m)).addHaar
 let D (i:Fin m):={q:OrbitSlice.Params m | (q i).2 i ≠ 0}
 have hn (i):μ (chart f i '' D i) = 0:=by
  apply OrbitSlice.Gw
  ·exact fun q hq=>(H7 f hf i q hq).differentiableWithinAt
  ·intro q c hc
   have hc0:c ≠ 0:=by intro h; simp [h] at hc
   have hw (z:ℂ):weight (c * z) = weight z:=by simp [weight,Complex.normSq_eq_norm_sq,hc]
   have hr:vF f i (Function.update q i ((q i).1,c • (q i).2)) = ((vF f i q).1,c • (vF f i q).2):=by
    have he:∀ j ∈ Finset.univ.erase i,Function.update q i ((q i).1,c • (q i).2) j = q j:=
     fun j hj=>Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _
    simp only [vF,Function.update_self,Finset.sum_congr rfl (fun j hj=>congrArg _ (he j hj)),rot c hc]
    ext k <;> simp [term,Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,hw] <;> simp only [mul_assoc,mul_left_comm _ c,← Finset.mul_sum] <;> ring
   funext j; by_cases hj:j = i
   ·subst j
    simp only [chart,Function.update_self,hr]
    ext k <;> simp [Pi.smul_apply,smul_eq_mul,hw] <;> field_simp <;> simp
   ·simp [chart,Function.update_of_ne hj]
 have hae:∀ᵐ p ∂μ,p ∉ ⋃ i,chart f i '' D i:=by
  rw [MeasureTheory.ae_iff]
  simpa only [not_not,Set.ofPred_mem_eq] using MeasureTheory.measure_iUnion_null hn
 obtain ⟨p,hp,hu⟩:=(MeasureTheory.Measure.dense_of_ae hae).inter_nhds_nonempty hU
 refine ⟨p,hu,fun x hz=>funext fun i=>?_⟩
 by_contra h
 exact hp (Set.mem_iUnion.mpr ⟨i,Function.update p i x,by simpa [D] using h,Ie f i x p h hz⟩)
end EilenbergGanea
end
noncomputable section
open Set Filter Topology MeasureTheory
open scoped ContDiff
open scoped ContDiff
open Set Filter Topology
namespace EilenbergGanea
def jM (n:ℕ):Fin n -> (Fin n -> ℝ):=fun i=>Pi.single i 1
def rH {n:ℕ} (form:(Fin (n + 1) -> ℝ) ->
  (Fin (n + 1) -> ℝ) [⋀^Fin n]→L[ℝ] ℝ) (i:Fin (n + 1))
  (x:Fin (n + 1) -> ℝ):ℝ:=
 (-1:ℝ) ^ i.val * form x (i.removeNth (jM (n + 1)))
private theorem JT {n:ℕ} (f:Fin (n+1) → (Fin (n+1) → ℝ) → ℝ)
    (hf:∀ i y,y 0 ∈ Icc (0:ℝ) 1 → DifferentiableAt ℝ (f i) y)
    (K:Set (Fin n → ℝ)) (hk:IsCompact K)
    (hs:∀ t ∈ Icc (0:ℝ) 1,∀ x,x ∉ K → ∀ i,f i (Fin.cons t x) = 0)
    (hz:∀ y,y 0 ∈ Icc (0:ℝ) 1 → ∑ i,fderiv ℝ (f i) y (Pi.single i 1) = 0) :
    (∫ x,f 0 (Fin.cons 1 x)) = ∫ x,f 0 (Fin.cons 0 x):=by
  classical
  obtain ⟨r,hr⟩:=(Metric.isBounded_iff_subset_ball 0).mp hk.isBounded
  let R:=max r 0
  have hR:0 ≤ R:=le_max_right _ _
  have bound {x} (hx:x ∈ K) (i:Fin n):-R < x i ∧ x i < R:=by
    apply abs_lt.mp
    exact (norm_le_pi_norm x i).trans_lt ((show ‖x‖ < r by simpa using hr hx).trans_le (le_max_left _ _))
  let A:Fin (n+1) → ℝ:=Fin.cons 0 (fun _:Fin n=>-R)
  let B:Fin (n+1) → ℝ:=Fin.cons 1 (fun _:Fin n=>R)
  have hle:A ≤ B:=Fin.forall_fin_succ.mpr ⟨zero_le_one,fun _=>neg_le_self hR⟩
  have time {y} (hy:y ∈ Icc A B):y 0 ∈ Icc (0:ℝ) 1:=⟨hy.1 0,hy.2 0⟩
  have hi:=setIntegral_eq_zero_of_forall_eq_zero (μ:=volume) (t:=Icc A B)
    (fun x hx=>hz x (time hx))
  have h:=integral_divergence_of_hasFDerivAt_off_countable' A B hle f
    (fun i=>fderiv ℝ (f i)) ∅ countable_empty
    (fun i x hx=>(hf i x (time hx)).continuousAt.continuousWithinAt)
    (fun x hx i=>(hf i x ⟨(hx.1 0 trivial).1.le,(hx.1 0 trivial).2.le⟩).hasFDerivAt)
    (integrableOn_zero.congr_fun (fun x hx=>(hz x (time hx)).symm) measurableSet_Icc)
  have side (i:Fin n) (c:ℝ) (hc:c = R ∨ c = -R) :
      (∫ x in Icc (A ∘ i.succ.succAbove) (B ∘ i.succ.succAbove),
        f i.succ (i.succ.insertNth c x)) = 0:=by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    let y:Fin (n+1) → ℝ:=i.succ.insertNth c x
    have hyt:y ∈ Icc A B:=Fin.insertNth_mem_Icc.mpr ⟨by rcases hc with rfl|rfl <;>
      simp [A,B,neg_le_self hR],hx⟩
    change f i.succ y = 0
    rw [← Fin.cons_self_tail (q:=y)]
    apply hs _ (time hyt)
    intro hy
    have hh:=bound hy i
    change -R < y i.succ ∧ y i.succ < R at hh
    simp only [y,Fin.insertNth_apply_same] at hh
    rcases hc with rfl | rfl
    · exact lt_irrefl _ hh.2
    · exact lt_irrefl _ hh.1
  have face (t:ℝ) (ht:t ∈ Icc (0:ℝ) 1):(∫ x in Icc (fun _:Fin n=>-R) (fun _=>R),f 0 (Fin.cons t x)) =
      ∫ x,f 0 (Fin.cons t x):=setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx=>
    hs _ ht _ (fun hK=>hx ⟨fun i=>(bound hK i).1.le,fun i=>(bound hK i).2.le⟩) _
  rw [hi] at h
  simp only [Fin.sum_univ_succ,A,B,Fin.cons_succ,Fin.cons_zero,
    side _ _ (Or.inl rfl),side _ _ (Or.inr rfl),Finset.sum_const_zero,add_zero,
    Fin.insertNth_zero',sub_self] at h
  rw [← face 1 (by simp),← face 0 (by simp)]
  exact sub_eq_zero.mp h.symm
theorem S7 {n:ℕ}
  (φ:(Fin n -> ℝ) -> (Fin n -> ℝ) [⋀^Fin n]→L[ℝ] ℝ) (x:Fin n -> ℝ) :
  extDeriv φ x=0:=by
 ext v
 apply (extDeriv φ x).toAlternatingMap.map_linearDependent
 intro hv
 have h:=hv.fintype_card_le_finrank
 simp at h
theorem k1 {n:ℕ} {E:Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (φ:(Fin n -> ℝ) -> (Fin n -> ℝ) [⋀^Fin n]→L[ℝ] ℝ)
  (hφ:Differentiable ℝ φ) (F:E -> (Fin n -> ℝ)) (hF:ContDiff ℝ 2 F) (x:E) :
  extDeriv (fun y=>(φ (F y)).compContinuousLinearMap (fderiv ℝ F y)) x=0:=by
 rw [extDeriv_pullback (hφ _) hF.contDiffAt (by simp),S7]
 ext v
 rfl
def k8 (n:ℕ):(Fin n -> ℝ) [⋀^Fin n]→L[ℝ] ℝ:=
 { Matrix.detRowAlternating with cont:=continuous_id.matrix_det }
theorem v6 {X A:Type*} [TopologicalSpace X] [Zero A]
  (U:Set X) (hU:IsOpen U) (f:X -> A)
  (x:X) (hb:x ∈ frontier U → x ∉ tsupport f) :
  U.indicator f =ᶠ[nhds x] f \/ U.indicator f =ᶠ[nhds x] fun _=>0:=by
 classical
 by_cases hx:x ∈ U
 ·left
  filter_upwards [hU.mem_nhds hx] with y hy
  exact Set.indicator_of_mem hy f
 ·right
  by_cases hc:x ∈ closure U
  ·have hf:x ∉ tsupport f:=by
    apply hb
    exact ⟨hc,by simpa only [hU.interior_eq] using hx⟩
   have he:=notMem_tsupport_iff_eventuallyEq.mp hf
   filter_upwards [he] with y hy
   by_cases hyU:y ∈ U <;> simp [Set.indicator,hyU,hy]
  ·filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hc] with y hy
   exact Set.indicator_of_notMem (fun hyU=>hy (subset_closure hyU)) f
theorem S8 {n:ℕ}
  (L:(Fin n -> ℝ) →L[ℝ] (Fin n -> ℝ)) :
  k8 n (fun i=>L (jM n i))=L.det:=by
 change Matrix.det (fun i=>L (Pi.single i 1))=_
 calc
  _=(LinearMap.toMatrix (Pi.basisFun ℝ (Fin n)) (Pi.basisFun ℝ (Fin n))
   L.toLinearMap).transpose.det:=by
    congr 1
  _=_:=by rw [Matrix.det_transpose,LinearMap.det_toMatrix]
theorem n6 {n:ℕ}
    (ρ:(Fin n -> ℝ) -> ℝ) (F:(Fin (n + 1) -> ℝ) -> (Fin n -> ℝ))
    (t:ℝ) (x:Fin n -> ℝ) (hF:DifferentiableAt ℝ F (Fin.cons t x)) :
    rH (fun y=>((ρ (F y)) • k8 n).compContinuousLinearMap
      (fderiv ℝ F y)) 0 (Fin.cons t x) =
      (fderiv ℝ (fun z=>F (Fin.cons t z)) x).det * ρ (F (Fin.cons t x)):=by
  let J:(Fin n -> ℝ) →L[ℝ] (Fin (n + 1) -> ℝ):=
    (0:(Fin n -> ℝ) →L[ℝ] ℝ).finCons (ContinuousLinearMap.id ℝ (Fin n -> ℝ))
  have hJ:HasFDerivAt (fun z:Fin n -> ℝ=>Fin.cons t z) J x:=
    (hasFDerivAt_const t x).finCons (hasFDerivAt_id x)
  have hs:=hF.hasFDerivAt.comp x hJ
  have he (i:Fin n):J (jM n i)=jM (n + 1) i.succ:=by
    funext j
    refine Fin.cases ?_ (fun k=>?_) j
    · simp [J,jM,ContinuousLinearMap.finCons]
    · simp [J,jM,ContinuousLinearMap.finCons,Pi.single_apply]
  have hs':fderiv ℝ (fun z=>F (Fin.cons t z)) x =
      (fderiv ℝ F (Fin.cons t x)).comp J:=hs.fderiv
  rw [hs']
  have hd:=S8 ((fderiv ℝ F (Fin.cons t x)).comp J)
  simp only [ContinuousLinearMap.comp_apply,he] at hd
  simp only [rH,Fin.val_zero,pow_zero,one_mul,Fin.removeNth_zero,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    ContinuousAlternatingMap.smul_apply,smul_eq_mul]
  rw [mul_comm]
  congr 1
theorem r5 {n:ℕ} {E:Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  (ρ:(Fin n -> ℝ) -> ℝ) (F:E -> (Fin n -> ℝ)) (hF:Continuous F) :
  tsupport (fun y=>((ρ (F y)) • k8 n).compContinuousLinearMap
   (fderiv ℝ F y)) ⊆ F ⁻¹' tsupport ρ:=by
 apply closure_minimal _ ((isClosed_tsupport ρ).preimage hF)
 intro x hx
 by_contra hn
 have hz:=image_eq_zero_of_notMem_tsupport hn
 exact hx (by ext v; simp [hz])
open Set MeasureTheory
theorem pC {n:ℕ}
  (ρ:(Fin n -> ℝ) -> ℝ) (hρ:Differentiable ℝ ρ)
  (F:(Fin (n + 1) -> ℝ) -> (Fin n -> ℝ)) (hF:ContDiff ℝ 2 F)
  (C:Set (Fin (n + 1) -> ℝ)) (hC:IsOpen C)
  (hboundary:∀ y ∈ frontier C,y 0 ∈ Icc (0:ℝ) 1 -> F y ∉ tsupport ρ)
  (hCb:Bornology.IsBounded {x:Fin n -> ℝ | ∃ t ∈ Icc (0:ℝ) 1,Fin.cons t x ∈ C}) :
  (∫ x in {x | (Fin.cons 1 x:Fin (n + 1) -> ℝ) ∈ C},
   (fderiv ℝ (fun z=>F (Fin.cons 1 z)) x).det * ρ (F (Fin.cons 1 x))) =
  ∫ x in {x | (Fin.cons 0 x:Fin (n + 1) -> ℝ) ∈ C},
   (fderiv ℝ (fun z=>F (Fin.cons 0 z)) x).det * ρ (F (Fin.cons 0 x)):=by
 classical
 let form:=fun y=>((ρ (F y)) • k8 n).compContinuousLinearMap
  (fderiv ℝ F y)
 have H x (ht:x 0 ∈ Icc (0:ℝ) 1):DifferentiableAt ℝ (C.indicator form) x ∧
   extDeriv (C.indicator form) x = 0:=by
  rcases v6 C hC form x (fun hy hs=>hboundary x hy ht (r5 ρ F hF.continuous hs)) with h | h <;>
   rw [h.extDeriv_eq]
  ·refine ⟨DifferentiableAt.congr_of_eventuallyEq ?_ h,k1 _ (hρ.smul_const _) F hF x⟩
   exact (((hρ _).comp x (hF.differentiable (by norm_num) x)).smul_const _).continuousAlternatingMapCompContinuousLinearMap
    ((hF.fderiv_right (m:=1) (by norm_num)).differentiable (by simp) x)
  ·refine ⟨(differentiableAt_const _).congr_of_eventuallyEq h,?_⟩
   ext v
   simp [extDeriv,ContinuousAlternatingMap.alternatizeUncurryFin_apply]
 let f i:=rH (C.indicator form) i
 have hf i x ht:DifferentiableAt ℝ (f i) x:=
  (differentiableAt_const _).mul ((H x ht).1.continuousAlternatingMap_apply_const _)
 have he:=JT f hf _ hCb.isCompact_closure (fun t ht x hx i=>by
  have hn:Fin.cons t x ∉ C:=fun h=>hx (subset_closure ⟨t,ht,h⟩)
  simp [f,rH,indicator_of_notMem hn]) (fun x ht=>by
  have h:=congrArg (fun A=>A (jM (n+1))) (H x ht).2
  have hx:=(H x ht).1
  rw [extDeriv_apply hx] at h
  convert h using 1 <;> try rfl
  apply Finset.sum_congr rfl
  intro i _
  change (fderiv ℝ (fun y=>(-1:ℝ)^i.val * (C.indicator form y) _) x) _ = _
  rw [fderiv_const_mul (hx.continuousAlternatingMap_apply_const _)]
  simp [jM])
 have hface (t:ℝ) (x:Fin n -> ℝ) :
   rH (C.indicator form) 0 (Fin.cons t x) =
    {x | (Fin.cons t x:Fin (n + 1) -> ℝ) ∈ C}.indicator
     (fun z=>(fderiv ℝ (fun w=>F (Fin.cons t w)) z).det *
     ρ (F (Fin.cons t z))) x:=by
  by_cases hx:(Fin.cons t x:Fin (n + 1) -> ℝ) ∈ C
  ·rw [indicator_of_mem (show x ∈ {x | (Fin.cons t x:Fin (n + 1) -> ℝ) ∈ C} from hx)]
   change (-1:ℝ) ^ (0:Fin (n + 1)).val *
    (C.indicator form) (Fin.cons t x) _=_
   rw [indicator_of_mem hx]
   exact n6 ρ F t x (hF.differentiable (by norm_num) _)
  ·simp [rH,hx]
 have hm (t:ℝ):MeasurableSet {x | (Fin.cons t x:Fin (n + 1) -> ℝ) ∈ C}:=by
  apply (hC.preimage _).measurableSet
  apply continuous_pi
  intro i
  exact Fin.cases continuous_const (fun j=>continuous_apply j) i
 simpa only [f,hface,integral_indicator (hm _)] using he
end EilenbergGanea
namespace EilenbergGanea
open Set MeasureTheory Filter Topology
private theorem xZ {X Y:Type*} [TopologicalSpace X] [MetricSpace Y]
  {L:Set X} (hL:IsCompact L) {S:Set (ℝ × X)} (hS:IsClosed S)
  {f:ℝ × X → Y} (hf:Continuous f) {y:Y}
  (avoid:∀ p ∈ Icc (0:ℝ) 1 ×ˢ L ∩ S,f p ≠ y) :
  ∃ r > 0,∀ p ∈ Icc (0:ℝ) 1 ×ˢ L ∩ S,r ≤ dist (f p) y:=by
 have hK:IsCompact (f '' (Icc (0:ℝ) 1 ×ˢ L ∩ S)):=(((isCompact_Icc.prod hL).inter_right hS).image hf)
 obtain ⟨r,hr,hball⟩:=Metric.isOpen_iff.mp hK.isClosed.isOpen_compl y
  (by rintro ⟨p,hp,he⟩; exact avoid p hp he)
 exact ⟨r,hr,fun p hp=>not_lt.mp fun h=>hball h ⟨p,hp,rfl⟩⟩
theorem S9 {n:ℕ}
    (F:(Fin (n + 1) -> ℝ) -> (Fin n -> ℝ)) (hF:ContDiff ℝ 2 F)
    (y:Fin n -> ℝ) (C:Set (Fin (n + 1) -> ℝ)) (hC:IsOpen C)
    (L:Set (Fin n → ℝ)) (hL:IsCompact L)
    (hbox:∀ t x,Fin.cons t x ∈ closure C → x ∈ L)
    (hb:∀ q ∈ frontier C,q 0 ∈ Icc (0:ℝ) 1 -> F q ≠ y)
    (a:Fin n → ℝ) (ha:Fin.cons 0 a ∈ C) (he:F (Fin.cons 0 a)=y) (c:ℝ)
    (hd:∀ x,Fin.cons 0 x ∈ C → F (Fin.cons 0 x)=y →
      0 < c * (fderiv ℝ (fun z=>F (Fin.cons 0 z)) x).det):∃ x,Fin.cons 1 x ∈ C ∧ F (Fin.cons 1 x)=y:=by
  classical
  by_contra hno
  have hno':∀ x,Fin.cons 1 x ∈ C -> F (Fin.cons 1 x) ≠ y:=by simpa using hno
  let U:ℝ -> Set (Fin n -> ℝ):=fun t=>{x | (Fin.cons t x:Fin (n + 1) -> ℝ) ∈ C}
  have hs (t:ℝ):U t ⊆ L:=fun x hx=>hbox t x (subset_closure hx)
  let J:=Fin.consEquivL ℝ (fun _:Fin (n+1)=>ℝ)
  let f₀:=fun x=>F (Fin.cons 0 x)
  let f₁:=fun x=>F (Fin.cons 1 x)
  have hcons (t:ℝ):ContDiff ℝ 2 (fun x:Fin n -> ℝ=>(Fin.cons t x:Fin (n + 1) -> ℝ)):=by
    apply contDiff_pi.mpr
    intro i
    exact Fin.cases contDiff_const (fun j=>contDiff_apply ℝ ℝ j) i
  have hU (t:ℝ):IsOpen (U t):=hC.preimage (hcons t).continuous
  have hf₀:ContDiff ℝ 1 f₀:=(hF.comp (hcons 0)).of_le (by norm_num)
  let d:=fun x=>c * (fderiv ℝ f₀ x).det
  have hdcont:Continuous d:=continuous_const.mul (ContinuousLinearMap.continuous_det.comp (hf₀.continuous_fderiv (by norm_num)))
  let bad:Set (ℝ × (Fin n → ℝ)):=J ⁻¹' closure C ∩
    (J ⁻¹' Cᶜ ∪ ({0} ×ˢ {x | d x ≤ 0}) ∪ ({1} ×ˢ univ))
  have closedBad:IsClosed bad:=(isClosed_closure.preimage J.continuous).inter
    (((hC.isClosed_compl.preimage J.continuous).union
      (isClosed_singleton.prod (isClosed_le hdcont continuous_const))).union
      (isClosed_singleton.prod isClosed_univ))
  obtain ⟨r,hr,clear⟩:=xZ hL closedBad (hF.continuous.comp J.continuous) (y:=y) (by
    rintro ⟨t,x⟩ ⟨⟨ht,hx⟩,hc,hs⟩ hz
    by_cases hin:J (t,x) ∈ C
    · rcases hs with (hout | ⟨rfl,hneg⟩) | ⟨rfl,_⟩
      · exact hout hin
      · exact (hd x hin hz).not_ge hneg
      · exact hno' x hin hz
    · exact hb _ (by rw [hC.frontier_eq]; exact ⟨hc,hin⟩) ht hz)
  let ρ:ContDiffBump y:=⟨r/4,r/2,by linarith,by linarith⟩
  have off (t:ℝ) (x) (ht:t ∈ Icc (0:ℝ) 1) (hx:(t,x) ∈ bad) :
      F (Fin.cons t x) ∉ tsupport ρ:=by
    rw [ρ.tsupport_eq]; intro hz
    exact (clear (t,x) ⟨⟨ht,hbox t x hx.1⟩,hx⟩).not_gt
      (lt_of_le_of_lt hz (by change r/2 < r; linarith))
  let w:=fun x=>d x * ρ (f₀ x)
  have hw:Continuous w:=hdcont.mul (ρ.continuous.comp hf₀.continuous)
  have hpos:0 < ∫ x in U 0,w x:=by
    apply (setIntegral_pos_iff_support_of_nonneg_ae _ _).2
    · apply ((hw.isOpen_support).inter (hU 0)).measure_pos volume
      refine ⟨a,?_,ha⟩
      change d a * ρ (f₀ a) ≠ 0
      rw [show f₀ a = y from he,ρ.one_of_mem_closedBall (Metric.mem_closedBall_self ρ.rIn_pos.le),mul_one]
      exact (hd a ha he).ne'
    · apply (ae_restrict_iff' (hU 0).measurableSet).mpr
      apply ae_of_all
      intro x hx
      by_cases hz:ρ (f₀ x) = 0
      · simp [w,hz]
      · apply mul_nonneg _ ρ.nonneg
        exact le_of_not_ge fun hn=>off 0 x (by simp)
          ⟨subset_closure hx,Or.inl (Or.inr ⟨rfl,hn⟩)⟩ (subset_tsupport _ hz)
    · exact (hw.continuousOn.integrableOn_compact hL).mono_set (hs 0)
  have hinv:=pC ρ (ρ.contDiff (n:=1) |>.differentiable (by simp)) F hF C hC (by
    intro q hq ht
    rw [hC.frontier_eq] at hq
    generalize heq:Fin.tail q = x at *
    have eq:Fin.cons (q 0) x = q:=heq ▸ Fin.cons_self_tail q
    rw [← eq] at hq ⊢
    exact off _ _ ht ⟨hq.1,Or.inl (Or.inl hq.2)⟩)
    (hL.isBounded.subset fun _ ⟨t,_,hx⟩=>hs t hx)
  have hzero:(∫ x in U 1,(fderiv ℝ f₁ x).det * ρ (f₁ x)) = 0:=by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    rw [image_eq_zero_of_notMem_tsupport (off 1 x (by simp)
      ⟨subset_closure hx,Or.inr ⟨rfl,trivial⟩⟩),mul_zero]
  have hz:(∫ x in U 0,(fderiv ℝ f₀ x).det * ρ (f₀ x)) = 0:=hinv.symm.trans hzero
  simp only [w,d,mul_assoc,integral_const_mul,hz,mul_zero,lt_self_iff_false] at hpos
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem wW
  (F:ℝ × E -> E) (hF:ContDiff ℝ 2 F) (y:E)
  (C:Set (ℝ × E)) (hC:IsOpen C)
  (L:Set E) (hL:IsCompact L) (hbox:∀ q ∈ closure C,q.2 ∈ L)
  (hb:∀ q ∈ frontier C,q.1 ∈ Icc (0:ℝ) 1 -> F q ≠ y)
  (a:E) (ha:(0,a) ∈ C) (he:F (0,a)=y) (c:ℝ)
  (hd:∀ x ∈ closure {z | (0,z) ∈ C},F (0,x)=y →
   0 < c * (fderiv ℝ (fun z=>F (0,z)) x).det):∃ x,(1,x) ∈ C ∧ F (1,x)=y:=by
 classical
 let n:=Module.finrank ℝ E
 let e:E ≃L[ℝ] (Fin n -> ℝ):=(Module.finBasis ℝ E).equivFunL
 let H:(ℝ × E) ≃L[ℝ] (Fin (n + 1) -> ℝ):=
  ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr e).trans (Fin.consEquivL ℝ (fun _=>ℝ))
 let G:(Fin (n + 1) -> ℝ) -> (Fin n -> ℝ):=fun q=>e (F (H.symm q))
 let D:=H.symm ⁻¹' C
 have hH (t:ℝ) (x:E):H (t,x)=Fin.cons t (e x):=rfl
 have hHi (t:ℝ) (x:Fin n -> ℝ):H.symm (Fin.cons t x)=(t,e.symm x):=by
  apply H.injective
  rw [H.apply_symm_apply,hH,e.apply_symm_apply]
 have hG:ContDiff ℝ 2 G:=e.contDiff.comp (hF.comp H.symm.contDiff)
 have hdet (x:E) :
   (fderiv ℝ (fun z=>G (Fin.cons 0 z)) (e x)).det =
   (fderiv ℝ (fun z=>F (0,z)) x).det:=by
  have h₀:DifferentiableAt ℝ (fun z=>F (0,z)) x:=
   (hF.comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num) x
  have h₀':HasFDerivAt (fun z=>F (0,z))
    (fderiv ℝ (fun z=>F (0,z)) x) (e.symm (e x)):=by
   simpa only [ContinuousLinearEquiv.symm_apply_apply] using h₀.hasFDerivAt
  have hcomp:=e.hasFDerivAt.comp (e x) (h₀'.comp (e x) e.symm.hasFDerivAt)
  have hh:(fun z=>G (Fin.cons 0 z))=e ∘ (fun z=>F (0,z)) ∘ e.symm:=by
   funext z; simp only [G,hHi,Function.comp_def]
  rw [hh,hcomp.fderiv]
  exact LinearMap.det_conj _ e.toLinearEquiv
 have hfront:frontier D=H.symm ⁻¹' frontier C:=by
  exact (H.symm.toHomeomorph.preimage_frontier C).symm
 obtain ⟨x,hx,he⟩:=S9 G hG (e y) D (hC.preimage H.symm.continuous)
  (e '' L) (hL.image e.continuous) (by
   intro t x hx
   have hh:H.symm.toHomeomorph ⁻¹' closure C = closure D:=H.symm.toHomeomorph.preimage_closure C
   rw [← hh] at hx
   change H.symm (Fin.cons t x) ∈ closure C at hx
   rw [hHi] at hx
   exact ⟨e.symm x,hbox _ hx,e.apply_symm_apply x⟩)
  (by
   intro q hq ht heq
   apply hb (H.symm q) (by rw [hfront] at hq; exact hq) ht
   exact e.injective heq) (e a) (by simpa [D,hHi] using ha) (by simpa [G,hHi] using congrArg e he) c (by
   intro z hz hzF
   have hx:(0,e.symm z) ∈ C:=by simpa only [D,mem_preimage,hHi] using hz
   have eq:=hdet (e.symm z)
   rw [e.apply_symm_apply] at eq
   rw [eq]
   exact hd _ (subset_closure hx) (e.injective (by simpa [G,hHi] using hzF)))
 exact ⟨e.symm x,by simpa only [D,mem_preimage,hHi] using hx,
  e.injective (by simpa only [G,hHi] using he)⟩
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
variable {E:Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
theorem oG
  (F:ℝ × E -> E) (hF:ContDiff ℝ 2 F)
  (C:Set (ℝ × E)) (hC:IsOpen C)
  (L:Set E) (hL:IsCompact L) (hbox:∀ q ∈ closure C,q.2 ∈ L)
  (hb:∀ q ∈ frontier C,q.1 ∈ Icc (0:ℝ) 1 -> F q ≠ 0)
  (a:E) (ha:(0,a) ∈ C) (c:ℝ)
  (happrox:∀ ε:ℝ,0 < ε -> ∃ g:E -> E,ContDiff ℝ ∞ g ∧
   (∀ x ∈ L,‖g x - F (0,x)‖ < ε) /\
   g a = 0 ∧ ∀ x ∈ closure {z | (0,z) ∈ C},g x=0 → 0 < c * (fderiv ℝ g x).det) :
  ∃ x,(1,x) ∈ C /\ F (1,x)=0:=by
 classical
 obtain ⟨ε,hε,clear⟩:=xZ hL isClosed_frontier hF.continuous (y:=0)
  (fun q hq=>hb q hq.2 hq.1.1)
 obtain ⟨g,hg,hclose,he,hd⟩:=happrox ε hε
 let G:ℝ × E -> E:=fun q=>F q + (1 - q.1) • (g q.2 - F (0,q.2))
 have hG:ContDiff ℝ 2 G:=hF.add
  ((contDiff_const.sub contDiff_fst).smul (((contDiff_infty.mp hg 2).comp contDiff_snd).sub
   (hF.comp (contDiff_const.prodMk contDiff_snd))))
 have hG0:(fun x=>G (0,x))=g:=by funext x; simp [G]
 have hGb:∀ q ∈ frontier C,q.1 ∈ Icc (0:ℝ) 1 -> G q ≠ 0:=by
  intro q hq ht he
  have heq:F q=-((1 - q.1) • (g q.2 - F (0,q.2))):=eq_neg_of_add_eq_zero_left he
  have hn:‖F q‖ < ε:=by
   rw [heq,norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith [ht.2])]
   calc
    (1 - q.1) * ‖g q.2 - F (0,q.2)‖ <= ‖g q.2 - F (0,q.2)‖:=
     mul_le_of_le_one_left (norm_nonneg _) (by linarith [ht.1])
    _ < ε:=hclose q.2 (hbox q (frontier_subset_closure hq))
  exact (clear q ⟨⟨ht,hbox _ (frontier_subset_closure hq)⟩,hq⟩).not_gt (by simpa using hn)
 obtain ⟨x,hx,he⟩:=wW G hG 0 C hC L hL hbox hGb a ha
  ((congrFun hG0 a).trans he) c (by simpa only [← hG0] using hd)
 exact ⟨x,hx,by simpa [G] using he⟩
end EilenbergGanea
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff
def dL {ι:Type*} {J:Type*} {m:ℕ}
  (w:J -> FreeGroup (ι ⊕ Fin m)) (a:ℝ -> ι -> a3)
  (q:ℝ × (Fin m -> a3)):J -> a3:=
 fun i=>FreeGroup.lift (Sum.elim (a q.1) q.2) (w i)
def cO {ι:Type*} {m:ℕ}:FreeGroup (ι ⊕ Fin m) →* FreeGroup (Fin m):=
 FreeGroup.lift (Sum.elim (fun _=>1) FreeGroup.of)
theorem k4 {ι:Type*} {J:Type*} {m:ℕ}
  (w:J -> FreeGroup (ι ⊕ Fin m)) (a:ℝ -> ι -> a3)
  (ha:∀ i,a 0 i=1) (x:Fin m -> a3) :
  dL w a (0,x)=fun i=>FreeGroup.lift x (cO (w i)):=by
 have he:FreeGroup.lift (Sum.elim (a 0) x)=(FreeGroup.lift x).comp cO:=by
  apply FreeGroup.ext_hom
  intro i
  cases i with
  | inl i=>simp [cO,ha]
  | inr i=>simp [cO]
 funext i
 exact congrArg (fun f:FreeGroup (ι ⊕ Fin m) →* a3=>f (w i)) he
end EilenbergGanea
namespace EilenbergGanea
open Set Filter Topology
open scoped Quaternion ContDiff
/- Polar-frame first variation of an unreduced toral word. -/
namespace RawSlice.Torus
noncomputable section
variable {n:Type}
def letter (b:Bool) (z:ℂ):ℂ:=if b then z else star z
def word (x:n → ℂ):List (n × Bool) → ℂ
 | []=>1
 | (j,b)::w=>letter b (x j) * word x w

def variation (v:n → ℂ):List (n × Bool) → ℂ
 | []=>0
 | (j,b)::w=>letter b (v j) + variation v w

theorem JX (x v:n → ℂ) (t:ℝ) (w:List (n × Bool)) :
  word (fun j=>x j * Complex.exp (t * v j)) w = word x w * Complex.exp (t * variation v w):=by
 induction w with
 | nil=>simp [word,variation]
 | cons l w ih=>obtain ⟨j,b⟩:=l; cases b <;>
   simp [word,variation,letter,ih,mul_add,Complex.exp_add,← Complex.exp_conj] <;> ring

variable [Fintype n] [DecidableEq n]
def exponent:List (n × Bool) → n → ℤ
 | [],_=>0
 | (k,b)::w,j=>(if k=j then (if b then 1 else -1) else 0) + exponent w j

theorem Jk (v:n → ℂ) (w:List (n × Bool)) :
 (variation v w).im = ∑ j,(exponent w j:ℝ)*(v j).im:=by
 induction w with
 | nil=>simp [exponent,variation]
 | cons l w ih=>obtain ⟨k,b⟩:=l; cases b <;> simp [exponent,variation,letter,ih,add_mul,Finset.sum_add_distrib,ite_mul]

def block (B:Matrix n n ℝ):=((2:ℝ) • (LinearMap.id:(n → ℝ) →ₗ[ℝ] (n → ℝ))).prodMap B.toLin'
theorem Jm (B:Matrix n n ℝ):(block B).det = 2^(Fintype.card n)*B.det:=by
 simp [block,LinearMap.det_prodMap,LinearMap.det_smul,LinearMap.det_toLin']

def lN:(n -> ℂ) ≃ₗ[ℝ] ((n -> ℝ) × (n -> ℝ)) where
 toFun z:=(fun i=>(z i).re,fun i=>(z i).im)
 invFun p i:=(p.1 i:ℂ) + (p.2 i:ℂ) * Complex.I
 left_inv z:=by funext i; exact Complex.re_add_im (z i)
 right_inv p:=by ext i <;> simp
 map_add' a b:=by ext i <;> simp
 map_smul' a b:=by ext i <;> simp
def i9 (x:n -> ℂ):(n -> ℂ) →L[ℝ] (n -> ℂ):=
 ((Matrix.diagonal x).toLin').toContinuousLinearMap.restrictScalars ℝ
@[simp] theorem SY (x z:n -> ℂ) (i:n) :
  i9 x z i=x i * z i:=by simp [i9,Matrix.toLin'_apply,Matrix.mulVec,Matrix.diagonal_apply,dotProduct]
theorem Tf (x:n -> ℂ) (hx:∀ i,‖x i‖=1) :
    (i9 x).toLinearMap.det=1:=by
  change (((Matrix.diagonal x).toLin').restrictScalars ℝ).det=_
  rw [LinearMap.det_restrictScalars,Algebra.norm_complex_apply,LinearMap.det_toLin',
    Matrix.det_diagonal]
  rw [Complex.normSq_eq_norm_sq,norm_prod]
  simp [hx]
end
end RawSlice.Torus
/- Based on openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
   Toral Fréchet derivative of the two polynomial slots. -/
namespace RawSlice.Torus
noncomputable section
variable {n:Type} [Fintype n] [DecidableEq n]
abbrev W:=n → List (n × Bool)
def B (w:W (n:=n)):Matrix n n ℝ:=fun i j=>exponent (w i) j
def pD (w:W (n:=n)) (x:n → ℂ) (i:n):ℂ:=⟨Complex.normSq (x i)-1,(word x (w i)).im⟩
theorem Jp (w : List (n × Bool)) : Differentiable ℝ (fun x : n → ℂ => word x w) := by
  induction w with
  | nil => exact differentiable_const _
  | cons l w ih => obtain ⟨i,b⟩ := l; cases b
                   · exact (Complex.conjCLE.differentiable.comp (differentiable_apply i)).mul ih
                   · exact (differentiable_apply i).mul ih

theorem Fv (w:W (n:=n)):Differentiable ℝ (pD w):=by
 apply differentiable_pi.mpr; intro i
 have he:(fun x=>pD w x i) = fun x=>((Complex.normSq (x i)-1:ℝ):ℂ) + (((word x (w i)).im:ℂ)*Complex.I):=by funext x; exact (Complex.re_add_im _).symm
 rw [he]
 have hn:Differentiable ℝ (fun x:n → ℂ=>Complex.normSq (x i)):=by
  simp only [Complex.normSq_apply]; fun_prop
 exact (Complex.ofRealCLM.differentiable.comp (hn.sub_const 1)).add ((Complex.ofRealCLM.differentiable.comp (Complex.imCLM.differentiable.comp (Jp _))).mul_const _)

def yW (w:W (n:=n)):=(((lN (n:=n)).symm.toLinearMap.comp (block (B w))).comp lN.toLinearMap).toContinuousLinearMap

theorem AG (w:W (n:=n)) (x:n → ℂ) (hx:∀ i,‖x i‖=1) (hw:∀ i,word x (w i)=1) :
  (fderiv ℝ (pD w) x).comp (i9 x) = yW w:=by
 ext v i:2
 let p (t:ℝ) (j:n):=x j * Complex.exp (t * v j)
 have ht:HasDerivAt (fun t:ℝ=>(t:ℂ)) 1 0:=Complex.ofRealCLM.hasDerivAt
 have e (z:ℂ):HasDerivAt (fun t:ℝ=>Complex.exp (t*z)) z 0:=by
  simpa using (ht.mul_const z).cexp
 have hp:HasDerivAt p (i9 x v) 0:=hasDerivAt_pi.mpr fun j=>by
  simpa [p] using (e (v j)).const_mul (x j)
 have h:=(Fv w (p 0)).hasFDerivAt.comp_hasDerivAt 0 hp
 have hi:=hasDerivAt_pi.mp h i
 have h0:p 0 = x:=by ext j; simp [p]
 rw [h0] at hi
 apply Complex.ext
 ·have d:=(Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 hi)
  have g:=(((hasDerivAt_id (0:ℝ)).mul_const (v i).re).exp.pow 2).sub_const 1
  have eqn:(fun t=>(pD w (p t) i).re) = (fun t:ℝ=>Real.exp (t*(v i).re)^2 - 1):=by
   funext t; simp [pD,p,Complex.normSq_eq_norm_sq,hx,Complex.norm_exp]
  change HasDerivAt (fun t=>(pD w (p t) i).re) _ _ at d
  rw [eqn] at d
  simpa [yW,block,lN] using d.unique g
 ·have d:=Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hi
  change HasDerivAt (fun t=>(word (p t) (w i)).im) _ _ at d
  simp only [p,JX,hw,one_mul] at d
  have g:=Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 (e (variation v (w i)))
  simpa [yW,block,B,lN,Jk,Matrix.toLin'_apply,Matrix.mulVec,dotProduct] using d.unique g

theorem Ih (w:W (n:=n)) (x:n → ℂ) (hx:∀ i,‖x i‖=1) (hw:∀ i,word x (w i)=1) :
  (fderiv ℝ (pD w) x).det=2^Fintype.card n*(B w).det:=by
 have h:=congrArg (fun L:(n → ℂ) →L[ℝ] (n → ℂ)=>L.toLinearMap.det) (AG w x hx hw)
 change ((fderiv ℝ (pD w) x).toLinearMap.comp (i9 x).toLinearMap).det=(((lN (n:=n)).symm.toLinearMap.comp (block (B w))).comp lN.toLinearMap).det at h
 rw [LinearMap.det_comp,Tf x hx,mul_one] at h
 exact h.trans ((LinearMap.det_conj _ lN.symm).trans (Jm _))
end
end RawSlice.Torus
section
open Set Filter Topology MeasureTheory
open scoped ContDiff
private theorem AH {m:ℕ} (f:Pair m → Pair m) (hf:ContDiff ℝ ∞ f)
    (rot:∀ (u:ℂ),‖u‖ = 1 → ∀ q,f (q.1,u • q.2) = ((f q).1,u • (f q).2))
    (r:ℝ) (hr:0 < r):∃ F:Pair m → Pair m,ContDiff ℝ ∞ F ∧
      (∀ q,‖F q - f q‖ < r) ∧
      (∀ (u:ℂ),‖u‖ = 1 → ∀ q,F (q.1,u • q.2) = ((F q).1,u • (F q).2)) ∧
      ∀ a,F (a,0) = f (a,0) ∧ (fderiv ℝ F (a,0)).det = (fderiv ℝ (r2 f) a).det:=by
  classical
  let J:=Prod.map (r2 f) (id:nZ m → nZ m)
  have ht:ContDiff ℝ ∞ (r2 f):=contDiff_fst.comp (hf.comp (contDiff_id.prodMk contDiff_const))
  let d:=J - f
  have hd:ContDiff ℝ ∞ d:=(ht.prodMap contDiff_id).sub hf
  let s (z:ℂ):=r^2 / (r^2 + Complex.normSq z)
  have pos z:=add_pos_of_pos_of_nonneg (sq_pos_of_pos hr) (Complex.normSq_nonneg z)
  have hs:ContDiff ℝ ∞ s:=by
    apply contDiff_const.div _ fun z=>(pos z).ne'
    simp only [Complex.normSq_apply,← Complex.reCLM_apply,← Complex.imCLM_apply]; fun_prop
  let S (v:nZ m) (i:Fin m):=s (v i) • v i
  have hS:ContDiff ℝ ∞ S:=by unfold S; fun_prop
  let T:=Prod.map S S
  let F:=f + T ∘ d
  refine ⟨F,hf.add ((hS.prodMap hS).comp hd),?_,?_,?_⟩
  · have b (v:nZ m):‖S v‖ < r:=(pi_norm_lt_iff hr).mpr fun i=>by
      simp only [S,s,norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (sq_nonneg r) (pos _).le),
        div_mul_eq_mul_div,div_lt_iff₀ (pos _)]
      rw [Complex.normSq_eq_norm_sq,sq r,mul_assoc,mul_lt_mul_iff_right₀ hr]
      nlinarith [sq_nonneg (r-‖v i‖),sq_pos_of_pos hr,sq_nonneg ‖v i‖]
    intro q; simpa [F,T,Prod.norm_def] using And.intro (b (d q).1) (b (d q).2)
  · intro u hu q
    have D:d (q.1,u • q.2) = ((d q).1,u • (d q).2):=by simp [d,J,rot u hu q,smul_sub]
    have h (v:nZ m):S (u • v) = u • S v:=by
      ext1 i; simp [S,s,Pi.smul_apply,Complex.normSq_eq_norm_sq,hu,mul_left_comm]
    simp [F,T,D,h,rot u hu q,smul_add]
  · intro a
    have z:(f (a,0)).2 = 0:=by
      funext i; exact CharZero.eq_neg_self_iff.mp (by simpa using congrFun (congrArg Prod.snd (rot (-1) (by simp) (a,0))) i)
    have zero:d (a,0) = 0:=sub_eq_zero.mpr (Prod.ext rfl z.symm:J (a,0) = f (a,0))
    refine ⟨by simp [F,T,zero,Prod.map_apply,S,Prod.zero_eq_mk]; rfl,?_⟩
    have I:HasFDerivAt S (.id ℝ _) 0:=hasFDerivAt_pi'.mpr fun i=>by
      change HasFDerivAt ((s ∘ fun v:nZ m=>v i) • fun v:nZ m=>v i) _ _
      simpa [s,hr.ne'] using (((hs.comp (contDiff_apply ℝ ℂ i)).differentiable (by simp) (0:nZ m)).hasFDerivAt.smul (hasFDerivAt_apply i (0:nZ m)))
    have I':HasFDerivAt T (.id ℝ _) (d (a,0)):=by rw [zero]; exact I.prodMap (p:=(0:Pair m)) I
    have A:=(hf.differentiable (by simp) (a,0)).hasFDerivAt
    have H:=(ht.differentiable (by simp) a).hasFDerivAt.prodMap (p:=(a,(0:nZ m))) (hasFDerivAt_id (𝕜:=ℝ) 0)
    have D:=(A.add (I'.comp _ (H.sub A))).fderiv
    rw [show fderiv ℝ F (a,0) = _ from D]; simp only [ContinuousLinearMap.id_comp,add_sub_cancel]
    change ((fderiv ℝ (r2 f) a).toLinearMap.prodMap (LinearMap.id:nZ m →ₗ[ℝ] nZ m)).det = _
    simp [LinearMap.det_prodMap]
theorem yZ {m:ℕ}
  (f:Pair m → Pair m) (hf:ContDiff ℝ ∞ f) (c:ℝ) (hc:c ≠ 0)
  (rot:∀ (u:ℂ),‖u‖ = 1 → ∀ q,f (q.1,u • q.2) = ((f q).1,u • (f q).2))
  (hone:f (1,0) = 0)
  (K:Set (Pair m))
  (hT:∀ a,(a,0) ∈ K → f (a,0) = 0 → (fderiv ℝ (r2 f) a).det = c)
  (L:Set ((Fin m -> ℂ) × (Fin m -> ℂ))) (hL:IsCompact L)
  (ε:ℝ) (hε:0 < ε) :
  ∃ g:((Fin m -> ℂ) × (Fin m -> ℂ)) -> ((Fin m -> ℂ) × (Fin m -> ℂ)),
   ContDiff ℝ ∞ g /\ (∀ q ∈ L,‖g q - f q‖ < ε) /\
   g (1,0) = 0 ∧ ∀ q ∈ K,g q=0 → 0 < c * (fderiv ℝ g q).det:=by
  classical
  obtain ⟨f₁,hf₁,hsmall,eqv,hreg⟩:=AH f hf rot (ε/2) (half_pos hε)
  obtain ⟨p,hp,hgood⟩:=Fp f₁ hf₁ eqv _ (D6 f₁ hf₁ L hL (ε/2) (half_pos hε))
  let g:=fun x=>lU f₁ x p
  have ax (a:nZ m):g (a,0)=f (a,0):=by rw [← (hreg a).1]; simp [g,lU,term,weight]
  have hg:ContDiff ℝ ∞ g:=(xW f₁ hf₁).comp (f:=fun x:Pair m=>(p,x)) (contDiff_const.prodMk contDiff_id)
  refine ⟨g,hg,?_,(ax 1).trans hone,?_⟩
  ·intro q hq
   have h₁:‖g q - f₁ q‖ < ε/2:=hp ⟨q,hq⟩
   exact (norm_sub_le_norm_sub_add_norm_sub (g q) (f₁ q) (f q)).trans_lt ((add_lt_add h₁ (hsmall q)).trans_eq (add_halves ε))
  ·intro ⟨a,b⟩ hk hz
   have hb:b = 0:=hgood (a,b) hz
   subst b
   rw [Er f₁ hf₁,(hreg a).2,hT a hk ((ax a).symm.trans hz)]
   exact mul_self_pos.mpr hc
end
section
open Set Filter Topology
open scoped ContDiff
abbrev nW (m:ℕ):=(Fin m → ℂ) × (Fin m → ℂ)
theorem zA {m:ℕ} (F:ℝ × nW m → nW m) (hF:ContDiff ℝ ∞ F)
  (h:ℝ × nW m → ℝ) (hh:Continuous h) (δ R:ℝ)
  (V:Set (ℝ × nW m)) (hV:IsOpen V)
  (h1:‖((1,0):nW m)‖ < R ∧ h (0,1,0) < δ ∧ (0,1,0) ∈ V)
  (hb:∀ q ∈ closure V,q.1 ∈ Icc (0:ℝ) 1 → F q = 0 → ‖q.2‖ < R ∧ h q ≠ δ ∧ q ∈ V)
  (f:nW m → nW m) (hf:∀ x,F (0,x) = f x)
  (rot:∀ (u:ℂ),‖u‖ = 1 → ∀ q,f (q.1,u • q.2) = ((f q).1,u • (f q).2))
  (hone:f (1,0) = 0) (c:ℝ) (hc:c ≠ 0)
  (hdet:∀ a,(0,a,0) ∈ closure V → f (a,0) = 0 → (fderiv ℝ (r2 f) a).det = c) :
  ∃ x,F (1,x) = 0 ∧ h (1,x) < δ ∧ (1,x) ∈ V:=by
 let C:={q:ℝ × nW m | ‖q.2‖ < R ∧ h q < δ ∧ q ∈ V}
 have hC:IsOpen C:=(isOpen_lt continuous_snd.norm continuous_const).inter ((isOpen_lt hh continuous_const).inter hV)
 have hcl:closure C ⊆ {q | ‖q.2‖ ≤ R ∧ h q ≤ δ ∧ q ∈ closure V}:=
  closure_minimal (fun _ hq=>⟨hq.1.le,hq.2.1.le,subset_closure hq.2.2⟩)
   ((isClosed_le continuous_snd.norm continuous_const).inter ((isClosed_le hh continuous_const).inter isClosed_closure))
 have hL:=isCompact_closedBall (0:nW m) R
 have hfront:∀ q ∈ frontier C,q.1 ∈ Icc (0:ℝ) 1 → F q ≠ 0:=by
  intro q hq ht hz
  have hq':=hcl (frontier_subset_closure hq)
  obtain ⟨hn,hd,hv⟩:=hb q hq'.2.2 ht hz
  exact hq.2 (by simpa only [hC.interior_eq] using (show q ∈ C from ⟨hn,lt_of_le_of_ne hq'.2.1 hd,hv⟩))
 let K:=closure {x:nW m | (0,x) ∈ C}
 have hKV:∀ x ∈ K,((0:ℝ),x) ∈ closure V:=closure_minimal
  (fun _ hx=>subset_closure hx.2.2) (isClosed_closure.preimage (continuous_const.prodMk continuous_id))
 have hsm:ContDiff ℝ ∞ f:=(funext hf) ▸ hF.comp (contDiff_const.prodMk contDiff_id)
 obtain ⟨x,hx,hz⟩:=oG F (contDiff_infty.mp hF 2) C hC _ hL
  (fun q hq=>Metric.mem_closedBall.mpr (by simpa using (hcl hq).1)) hfront (1,0) h1 c (by
   intro ε hε
   simpa only [hf] using yZ f hsm c hc rot hone K
    (fun a hk=>hdet a (hKV _ hk))
    _ hL ε hε)
 exact ⟨x,hz,hx.2⟩
end

/- Adapted from openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
namespace PolyFamily
open Set Filter Topology
open scoped Quaternion ContDiff
noncomputable section
def spell {α:Type*} (f:α → ℍ):List (α × Bool) → ℍ
 | []=>1
 | (i,b)::ls=>(if b then f i else star (f i)) * spell f ls

def strip {ι V:Type*}:List ((ι ⊕ V) × Bool) → List (V × Bool)
 | []=>[]
 | (.inl _,_)::ls=>strip ls
 | (.inr j,b)::ls=>(j,b)::strip ls

theorem zQ {ι V:Type*} (f:V → ℍ) (ls:List ((ι ⊕ V) × Bool)) :
  spell (Sum.elim (fun _=>1) f) ls = spell f (strip ls):=by
 induction ls with
 | nil=>rfl
 | cons l ls ih=>
  obtain ⟨i,b⟩:=l
  cases i <;> cases b <;> simp [strip,spell,Sum.elim,ih]


variable {ι:Type*} {J:Type*} {m:ℕ}
abbrev X (m:ℕ):=(Fin m → ℂ) × (Fin m → ℂ)
def raw (w:J → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (q:ℝ × X m) (i:J):=by
 classical exact spell (Sum.elim (fun k=>(a q.1 k:ℍ)) (aP.symm q.2)) (w i).toWord

def slots (x z:ℍ):ℍ:=⟨Quaternion.normSq x-1,z.imI,z.imJ,z.imK⟩
def eqs (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (q:ℝ × X m):X m:=
 aP (fun i=>slots (aP.symm q.2 i) (raw w a q i))
def pure (s:Fin m → List (Fin m × Bool)) (x:X m):X m:=
 aP (fun i=>slots (aP.symm x i) (spell (aP.symm x) (s i)))
theorem initial (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (ha:∀ i,a 0 i=1) (x:X m) :
  eqs w a (0,x) = pure (fun i=>strip (letI:=Classical.decEq ι; (w i).toWord)) x:=by
 classical simp [eqs,raw,pure,ha,zQ]

theorem Et {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → ι → ℍ)
    (hf : ∀ i, ContDiff ℝ ∞ (fun x => f x i)) (l : List (ι × Bool)) : ContDiff ℝ ∞ (fun x => spell (f x) l) := by
  induction l with
  | nil => exact contDiff_const
  | cons l w ih => obtain ⟨i,b⟩ := l; cases b
                   · let L : ℍ →ₗ[ℝ] ℍ := { toFun := star, map_add' := star_add, map_smul' := Quaternion.star_smul }
                     exact (L.toContinuousLinearMap.contDiff.comp (hf i)).mul ih
                   · exact (hf i).mul ih

theorem vG (w:J → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (ha:∀ i,ContDiff ℝ ∞ (fun t=>(a t i:ℍ))) (i:J):ContDiff ℝ ∞ (fun q=>raw w a q i):=by
 classical apply Et; intro j; cases j with
 | inl k=>exact (ha k).comp contDiff_fst
 | inr k=>exact (contDiff_apply ℝ ℍ k).comp (aP.symm.contDiff.comp contDiff_snd)

theorem Ew:ContDiff ℝ ∞ (fun p:ℍ × ℍ=>slots p.1 p.2):=by
 let reL:ℍ →ₗ[ℝ] ℝ:={ toFun:=QuaternionAlgebra.re,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }
 let inc:ℝ →ₗ[ℝ] ℍ:={ toFun:=fun x:ℝ=>(x:ℍ),map_add':=Quaternion.coe_add,map_smul':=fun _ _=>by ext <;> simp }
 have he:(fun p:ℍ × ℍ=>slots p.1 p.2) = fun p=>inc (‖p.1‖^2 - 1 - reL p.2) + p.2:=by
  funext p; apply Quaternion.ext
  ·change Quaternion.normSq p.1-1 = (‖p.1‖^2-1-p.2.re)+p.2.re; rw [Quaternion.normSq_eq_norm_mul_self]; ring
  all_goals (change _ = 0 + _; rw [zero_add]; rfl)
 rw [he]; exact (inc.toContinuousLinearMap.contDiff.comp (((contDiff_fst.norm_sq ℝ).sub contDiff_const).sub (reL.toContinuousLinearMap.contDiff.comp contDiff_snd))).add contDiff_snd

theorem Ij (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (ha:∀ i,ContDiff ℝ ∞ (fun t=>(a t i:ℍ))):ContDiff ℝ ∞ (eqs w a):=by
 apply aP.contDiff.comp; apply contDiff_pi.mpr; intro i
 exact Ew.comp (((contDiff_apply ℝ ℍ i).comp (aP.symm.contDiff.comp contDiff_snd)).prodMk (vG w a ha i))

theorem zR (x:Fin m → ℂ) (l:List (Fin m × Bool)):spell (fun i=>Quaternion.ofComplex (x i)) l = Quaternion.ofComplex (RawSlice.Torus.word x l):=by
 induction l with
 | nil=>simp [spell,RawSlice.Torus.word]
 | cons l w ih=>obtain ⟨i,b⟩:=l; cases b <;> simp only [spell,RawSlice.Torus.word,RawSlice.Torus.letter,if_true,if_false,Bool.false_eq_true,ih,map_mul,reduceIte] <;> congr 1 <;> apply Quaternion.ext <;> simp

theorem axis (s:Fin m → List (Fin m × Bool)):r2 (pure s)=RawSlice.Torus.pD s:=by
  funext x i; unfold r2 pure; rw [n7]; apply Complex.ext
  · change Quaternion.normSq (Quaternion.ofComplex (x i))-1=Complex.normSq (x i)-1
    rw [Quaternion.normSq_eq_norm_mul_self,k9,Complex.normSq_eq_norm_sq,pow_two]
  · change (spell (fun j=>Quaternion.ofComplex (x j)) (s i)).imI = _; rw [zR x]; rfl
end
end PolyFamily
/- Based on openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
   The unreduced stripped spelling has the exponent matrix of the erased word. -/
namespace PolyFamily
open RawSlice.Torus
noncomputable section
variable {ι:Type*} {m:ℕ}
def expHom (j:Fin m):FreeGroup (Fin m) →* Multiplicative ℤ:=
 FreeGroup.lift (fun k=>Multiplicative.ofAdd (if j=k then (1:ℤ) else 0))

theorem Dm (L:List ((ι ⊕ Fin m) × Bool)) (j:Fin m) :
  exponent (strip L) j = Multiplicative.toAdd (expHom j (cO (FreeGroup.mk L))):=by
 induction L with
 | nil=>simp [strip,exponent,← FreeGroup.one_eq_mk]
 | cons l L ih=>
  obtain ⟨i,b⟩:=l
  have hm:FreeGroup.mk ((i,b)::L) = FreeGroup.mk [(i,b)] * FreeGroup.mk L:=by
   rw [FreeGroup.mul_mk]; rfl
  rw [hm,map_mul,map_mul,toAdd_mul,← ih]
  cases i with
  | inl k=>cases b <;> simp [strip,cO,FreeGroup.lift_mk]
  | inr k=>cases b <;> simp [strip,exponent,expHom,cO,FreeGroup.lift_mk,eq_comm] <;> split_ifs <;> simp

theorem CX (w:Fin m → FreeGroup (ι ⊕ Fin m)) :
  B (n:=Fin m) (fun i=>letI:=Classical.decEq ι; strip (w i).toWord) =
   (c8 (fun i=>cO (w i))).map (Int.cast:ℤ → ℝ):=by
 classical
 funext i j
 simp only [B,Matrix.map_apply]
 congr 1
 rw [Dm,FreeGroup.mk_toWord]; rfl
end
end PolyFamily
/- Based on openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
   Circle equivariance of the unreduced pure polynomial map. -/
namespace PolyFamily
open scoped Quaternion
noncomputable section
variable {m:ℕ}
theorem conj_mul (a:a3) (p q:ℍ) :
  aY a (p*q) = aY a p * aY a q:=by
 have h:star (a:ℍ) * (a:ℍ) = 1:=Unitary.star_mul_self_of_mem a.property
 simp only [aY]
 calc (a:ℍ)*(p*q)*star (a:ℍ) = (a:ℍ)*p*(star (a:ℍ)*(a:ℍ))*q*star (a:ℍ):=by rw [h]; noncomm_ring
  _ = _:=by noncomm_ring

theorem Jq (a:a3) (p:ℍ):aY a (star p) = star (aY a p):=by
 simp [aY,star_mul,mul_assoc]

theorem K5 (p q:ℍ):(p*q).re = (q*p).re:=by
 simp only [Quaternion.re_mul]; ring

theorem conj_re (a:a3) (p:ℍ):(aY a p).re = p.re:=by
 have h:star (a:ℍ) * (a:ℍ) = 1:=Unitary.star_mul_self_of_mem a.property
 simp only [aY]
 rw [K5,← mul_assoc,h,one_mul]

theorem Io (a:a3) (x:Fin m → ℍ) (l:List (Fin m × Bool)) :
  spell (fun i=>aY a (x i)) l = aY a (spell x l):=by
 induction l with
 | nil=>simp [spell]
 | cons l w ih=>obtain ⟨i,b⟩:=l; cases b <;> simp [spell,ih,conj_mul,Jq]

theorem Ez (x z:ℍ):slots x z = ((Quaternion.normSq x-1-z.re:ℝ):ℍ) + z:=by
 apply Quaternion.ext
 ·change Quaternion.normSq x-1 = (Quaternion.normSq x-1-z.re)+z.re; ring
 all_goals (change _ = 0 + _; rw [zero_add]; rfl)

theorem Ip (a:a3) (x z:ℍ) :
  slots (aY a x) (aY a z) = aY a (slots x z):=by
 have hn:Quaternion.normSq (aY a x) = Quaternion.normSq x:=by
  rw [Quaternion.normSq_eq_norm_mul_self,Quaternion.normSq_eq_norm_mul_self,h7]
 rw [Ez,Ez,hn,conj_re]
 simp only [aY,mul_add,add_mul]
 congr 1
 have h:(a:ℍ) * star (a:ℍ) = 1:=Unitary.mul_star_self_of_mem a.property
 rw [← Quaternion.coe_commutes,mul_assoc,h,mul_one]

theorem J4 (s:Fin m → List (Fin m × Bool)) (u:ℂ) (hu:‖u‖ = 1) (q:X m) :
  pure s (q.1,u • q.2) = ((pure s q).1,u • (pure s q).2):=by
 obtain ⟨c,hc⟩:=S6 u hu
 let x:=aP.symm q
 have hx:aP x = q:=aP.apply_symm_apply q
 have heq:aP.symm (q.1,u • q.2) = fun i=>aY (vV c) (x i):=by
  apply aP.injective
  rw [ContinuousLinearEquiv.apply_symm_apply,i5,hc,hx]
 unfold pure
 rw [heq]
 simp only [Io,Ip]
 rw [i5,hc]
end
end PolyFamily
/- Based on openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
   Moving-domain application of the unreduced polynomial family (no cutoffs). -/
namespace PolyFamily
open Set Filter Topology
open scoped Quaternion ContDiff
noncomputable section
variable {ι:Type*} {J:Type*} {m:ℕ}
theorem Iq {α:Type*} (f:α → a3) (L:List (α × Bool)) :
  ((FreeGroup.lift f (FreeGroup.mk L):a3):ℍ) = spell (fun i=>(f i:ℍ)) L:=by
 induction L with
 | nil=>simp [spell,← FreeGroup.one_eq_mk]
 | cons l L ih=>
  obtain ⟨i,b⟩:=l
  have hm:FreeGroup.mk ((i,b)::L) = FreeGroup.mk [(i,b)] * FreeGroup.mk L:=by
   rw [FreeGroup.mul_mk]; rfl
  rw [hm,map_mul]
  change ((FreeGroup.lift f (FreeGroup.mk [(i,b)]):a3):ℍ) * ((FreeGroup.lift f (FreeGroup.mk L):a3):ℍ) = _
  rw [ih]
  cases b <;> simp [spell,FreeGroup.lift_mk]
  exact Or.inl rfl

theorem zC (w:J → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (q:ℝ × X m)
  (x:Fin m → a3) (hx:aP.symm q.2 = fun i=>(x i:ℍ)) (i:J) :
  raw w a q i = (dL w a (q.1,x) i:ℍ):=by
 classical
 have he:Sum.elim (fun k=>(a q.1 k:ℍ)) (aP.symm q.2) =
   fun j=>((Sum.elim (a q.1) x j:a3):ℍ):=by
  funext j; cases j <;> simp [hx]
 unfold raw dL
 rw [he,← Iq,FreeGroup.mk_toWord]

theorem Iw {x z:ℍ} (h:slots x z = 0) :
  Quaternion.normSq x = 1 ∧ z.imI = 0 ∧ z.imJ = 0 ∧ z.imK = 0:=by
 have h0:=congrArg QuaternionAlgebra.re h
 change Quaternion.normSq x - 1 = 0 at h0
 exact ⟨by linarith,congrArg QuaternionAlgebra.imI h,congrArg QuaternionAlgebra.imJ h,congrArg QuaternionAlgebra.imK h⟩

theorem ED (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (q:ℝ × X m)
  (hq:eqs w a q = 0) (i:Fin m) :
  slots (aP.symm q.2 i) (raw w a q i) = 0:=by
 have h:(fun i=>slots (aP.symm q.2 i) (raw w a q i)) = 0:=
  aP.injective (by rw [map_zero]; exact hq)
 exact congrFun h i

theorem Dp {y:ℍ} (h:Quaternion.normSq y = 1):‖y‖ = 1:=by
 rw [Quaternion.normSq_eq_norm_mul_self] at h; nlinarith [norm_nonneg y]

theorem Dq {y:ℍ} (h:‖y‖ = 1):((bT y:a3):ℍ) = y:=by
 rw [c1 (by intro hz; simp [hz] at h),h,inv_one,one_smul]

/-- Roots in the closed positive region: unit spatial letters and every raw word equal to one. -/
theorem zD {z u:ℍ} (hz:slots u z = 0) (hn:‖z‖ = 1) (hp:0 ≤ z.re):z = 1:=by
 have hi:z.imI = 0:=congrArg QuaternionAlgebra.imI hz
 have hj:z.imJ = 0:=congrArg QuaternionAlgebra.imJ hz
 have hk:z.imK = 0:=congrArg QuaternionAlgebra.imK hz
 have he:z = (z.re:ℍ):=Quaternion.ext _ _ rfl hi hj hk
 have hr:z.re = 1:=by
  have h:=(congrArg norm he).symm.trans hn
  simpa only [Quaternion.norm_coe,Real.norm_eq_abs,abs_of_nonneg hp] using h
 simpa only [hr,Quaternion.coe_one] using he

theorem pJ (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (q:ℝ × X m)
  (hq:eqs w a q = 0) (hp:∀ i,0 ≤ (raw w a q i).re) :
  (∀ i,‖aP.symm q.2 i‖ = 1) ∧
  aP.symm q.2 = (fun i=>(bT (aP.symm q.2 i):ℍ)) ∧
  dL w a (q.1,fun i=>bT (aP.symm q.2 i)) = 1:=by
 have hn i:=Dp (Iw (ED w a q hq i)).1
 have hy:aP.symm q.2 = (fun i=>(bT (aP.symm q.2 i):ℍ)):=
  funext fun i=>(Dq (hn i)).symm
 refine ⟨hn,hy,funext fun i=>Subtype.ext ?_⟩
 have hr:=zC w a q _ hy i
 have hz:=ED w a q hq i
 have hpi:=hp i
 rw [hr] at hz hpi
 exact zD (u:=aP.symm q.2 i) hz ((c9 _).mp (Subtype.property _)) hpi

theorem Jr (x:Fin m → ℂ) (hx:∀ i,‖x i‖ = 1) (l:List (Fin m × Bool)) :
  ‖RawSlice.Torus.word x l‖ = 1:=by
 induction l with
 | nil=>simp [RawSlice.Torus.word]
 | cons l w ih=>obtain ⟨i,b⟩:=l; cases b <;> simp [RawSlice.Torus.word,RawSlice.Torus.letter,hx,ih]

theorem Fw {z:ℂ} (hn:‖z‖ = 1) (hi:z.im = 0) (hr:0 ≤ z.re):z = 1:=by
 have he:z = (z.re:ℂ):=Complex.ext rfl (by simp [hi])
 rw [he] at hn ⊢
 rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr] at hn
 simp [hn]

def V (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3):Set (ℝ × X m):={q | ∀ i,0 < (raw w a q i).re}

theorem V_open (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (ha:∀ i,ContDiff ℝ ∞ (fun t=>(a t i:ℍ))) :
  IsOpen (V w a):=by
 simp only [V,ofPred_forall]
 exact isOpen_iInter_of_finite fun i=>isOpen_lt continuous_const
  (Quaternion.continuous_re.comp (vG w a ha i).continuous)

theorem DN (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (ha:∀ i,ContDiff ℝ ∞ (fun t=>(a t i:ℍ)))
  {q} (hq:q ∈ closure (V w a)) (i:Fin m):0 ≤ (raw w a q i).re:=
 closure_minimal (fun _ hx=>(hx i).le)
  (isClosed_le continuous_const (Quaternion.continuous_re.comp (vG w a ha i).continuous)) hq

/-- K-local toral determinant: on the closed positive region the axis roots are toral roots of the stripped words. -/
theorem J6 (w:Fin m → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3) (ha0:∀ i,a 0 i = 1)
  (x:Fin m → ℂ) (hp:∀ i,0 ≤ (raw w a (0,x,0) i).re)
  (hz:pure (fun i=>strip (letI:=Classical.decEq ι; (w i).toWord)) (x,0) = 0) :
  (fderiv ℝ (r2 (pure (fun i=>strip (letI:=Classical.decEq ι; (w i).toWord)))) x).det =
   2^m * ((c8 (fun i=>cO (w i))).det:ℝ):=by
 set s:=fun i=>strip (letI:=Classical.decEq ι; (w i).toWord)
 have hr:RawSlice.Torus.pD s x = 0:=by
  rw [← axis s]; exact congrArg Prod.fst hz
 have hn i:‖x i‖ = 1:=by
  have h:=congrArg Complex.re (congrFun hr i)
  change Complex.normSq (x i) - 1 = 0 at h
  rw [Complex.normSq_eq_norm_sq] at h; nlinarith [norm_nonneg (x i)]
 have hw i:RawSlice.Torus.word x (s i) = 1:=by
  have hi:=congrArg Complex.im (congrFun hr i)
  change (RawSlice.Torus.word x (s i)).im = 0 at hi
  have hre:=hp i
  have he:raw w a (0,x,0) i = Quaternion.ofComplex (RawSlice.Torus.word x (s i)):=by
   unfold raw; rw [← zR]
   classical
   rw [n7]; convert zQ (ι:=ι) (fun j=>Quaternion.ofComplex (x j)) _ using 2
   funext j; cases j <;> simp [ha0]
  rw [he] at hre
  exact Fw (Jr x hn _) hi hre
 rw [axis s,RawSlice.Torus.Ih s x hn hw,CX,Fintype.card_fin]
 congr 1; exact (RingHom.map_det (Int.castRingHom ℝ) _).symm
end
end PolyFamily
namespace PolyFamily
theorem Jt {α:Type*} (l:List (α × Bool)):spell (fun _=>(1:ℍ)) l = 1:=by
 induction l with
 | nil=>rfl
 | cons l w ih=>obtain ⟨i,b⟩:=l; cases b <;> simp [spell,ih]

end PolyFamily
open PolyFamily in
theorem F9 {ι:Type*} {J:Type*} {m:ℕ} (v:J → FreeGroup (ι ⊕ Fin m)) (a:ℝ → ι → a3)
  (ha0:∀ i,a 0 i=1) (i:J):raw v a (0,1,0) i = 1:=by
 have hx:aP.symm ((1,0):X m) = fun i=>((1:Fin m → a3) i:ℍ):=by
  rw [n7]; funext i; simp
 rw [zC v a _ 1 hx,k4 v a ha0]
 have hl:FreeGroup.lift (1:Fin m -> a3) = 1:=FreeGroup.ext_hom _ _ fun i=>by simp
 rw [hl]; rfl
open PolyFamily in
theorem Tj {ι:Type*} {J:Type*} [Fintype J] {m:ℕ}
    (w:Fin m -> FreeGroup (ι ⊕ Fin m)) (ρ:J -> FreeGroup (ι ⊕ Fin m))
    (a:ℝ -> ι -> a3) (ha:∀ i,ContDiff ℝ ∞ (fun t=>(a t i:ℍ)))
    (ha0:∀ i,a 0 i=1)
    (hB:(c8 (fun i=>cO (w i))).det ≠ 0)
    (δ:ℝ) (hδ:0 < δ)
    (hiso:∀ t ∈ Icc (0:ℝ) 1,∀ x:Fin m -> a3,
      dL w a (t,x)=1 ->
      ‖(fun i=>(dL ρ a (t,x) i:ℍ)) - 1‖ ≠ δ) :
    ∃ x:Fin m -> a3,dL w a (1,x)=1 /\
      ‖(fun i=>(dL ρ a (1,x) i:ℍ)) - 1‖ < δ:=by
  classical
  let e:(Fin m → ℍ) ≃L[ℝ] X m:=aP
  let s:=fun i=>strip (letI:=Classical.decEq ι; (w i).toWord)
  let h:ℝ × X m → ℝ:=fun q=>‖(fun i=>raw ρ a q i) - 1‖
  have hh:Continuous h:=((continuous_pi fun i=>(vG ρ a ha i).continuous).sub continuous_const).norm
  -- bounded unit roots
  let R:ℝ:=‖e.toContinuousLinearMap‖ + ‖((1:Fin m -> ℂ),(0:Fin m -> ℂ))‖ + 1
  have hnorm (q:ℝ × X m) (hu:∀ i,‖e.symm q.2 i‖ = 1):‖q.2‖ < R:=by
    have hle:‖e.symm q.2‖ ≤ 1:=(pi_norm_le_iff_of_nonneg (by positivity)).mpr fun i=>(hu i).le
    have:‖q.2‖ ≤ ‖e.toContinuousLinearMap‖:=
      calc ‖q.2‖ = ‖e (e.symm q.2)‖:=by rw [e.apply_symm_apply]
        _ ≤ ‖e.toContinuousLinearMap‖ * ‖e.symm q.2‖:=e.toContinuousLinearMap.le_opNorm _
        _ ≤ _:=mul_le_of_le_one_right (norm_nonneg e.toContinuousLinearMap) hle
    have:=norm_nonneg ((1:Fin m -> ℂ),(0:Fin m -> ℂ)); dsimp only [R]; linarith
  have hsize (q:ℝ × X m) (hq:eqs w a q = 0) (hp:∀ i,0 ≤ (raw w a q i).re) :
      h q = ‖(fun i=>(dL ρ a (q.1,fun j=>bT (e.symm q.2 j)) i:ℍ)) - 1‖:=by
    obtain ⟨_,hy,_⟩:=pJ w a q hq hp
    dsimp only [h]; congr 2; funext i; exact zC ρ a q _ hy i
  have hc:(2:ℝ)^m * ((c8 (fun i=>cO (w i))).det:ℝ) ≠ 0:=
    mul_ne_zero (pow_ne_zero _ two_ne_zero) (by exact_mod_cast hB)
  obtain ⟨x,hx,hhx,hV⟩:=zA (eqs w a) (Ij w a ha) h hh δ R (V w a) (V_open w a ha)
    ⟨by have:=norm_nonneg e.toContinuousLinearMap; dsimp only [R]; linarith,
     by dsimp only [h]; rw [show (fun i=>raw ρ a (0,1,0) i) = 1 from funext (F9 ρ a ha0),sub_self,norm_zero]; exact hδ,
     fun i=>by rw [F9 w a ha0]; norm_num⟩
    (by
      intro q hq ht hz
      have hp:=DN w a ha hq
      obtain ⟨hu,_,hc1⟩:=pJ w a q hz hp
      refine ⟨hnorm q hu,?_,?_⟩
      · rw [hsize q hz hp]; exact hiso q.1 ht _ hc1
      · intro i
        obtain ⟨_,hy,_⟩:=pJ w a q hz hp
        rw [zC w a q _ hy i,hc1]; norm_num)
    (PolyFamily.pure s) (fun x=>initial w a ha0 x) (J4 s) (by
      have:PolyFamily.pure s ((1:Fin m → ℂ),0) = aP (fun _=>slots 1 1):=by
        unfold PolyFamily.pure; rw [n7]; congr 1; funext i
        rw [show (fun j:Fin m=>Quaternion.ofComplex ((1:Fin m → ℂ) j)) = fun _=>(1:ℍ) from funext fun _=>by simp,Jt]
      rw [this]; rw [show (fun _:Fin m=>slots 1 1) = 0 from funext fun _=>by ext <;> simp [slots]]; exact map_zero _)
    _ hc (fun z hz h0=>J6 w a ha0 z (DN w a ha hz) h0)
  have hp:∀ i,0 ≤ (raw w a (1,x) i).re:=fun i=>(hV i).le
  exact ⟨_,(pJ w a (1,x) hx hp).2.2,(hsize (1,x) hx hp) ▸ hhx⟩
end EilenbergGanea
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea
open scoped Quaternion ContDiff
def oK (a:a3) (t:ℝ):ℍ:=
 (1 - Real.smoothTransition t) • (1:ℍ) + Real.smoothTransition t • (a:ℍ)
theorem q8 (a:a3) (t:ℝ) :
  ‖oK a t - 1‖ ≤ ‖(a:ℍ) - 1‖:=by
 have he:oK a t - 1 = Real.smoothTransition t • ((a:ℍ) - 1):=by
  rw [oK,sub_smul,one_smul,smul_sub]
  abel
 rw [he,norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.smoothTransition.nonneg t)]
 exact mul_le_of_le_one_left (norm_nonneg _) (Real.smoothTransition.le_one t)
theorem Cr (a:a3) (ha:‖(a:ℍ) - 1‖ < 1) (t:ℝ) :
  oK a t ≠ 0:=by
 intro he
 simpa [he] using (q8 a t).trans_lt ha
def jU (a:a3) (t:ℝ):a3:=bT (oK a t)
@[simp] theorem dj5 (a:a3):jU a 0=1:=by
 simpa [jU,oK] using (SX (1:a3))
@[simp] theorem dk7 (a:a3):jU a 1=a:=by
 simp [jU,oK]
theorem Tk (a:a3) (ha:‖(a:ℍ) - 1‖ < 1) :
  ContDiff ℝ ∞ (fun t=>(jU a t:ℍ)):=by
 apply contDiff_iff_contDiffAt.mpr
 intro t
 exact (g5 (Cr a ha t)).comp t
  (((contDiff_const.sub Real.smoothTransition.contDiff).smul contDiff_const).add
   (Real.smoothTransition.contDiff.smul contDiff_const)).contDiffAt
theorem qM (u:ℍ) :
  ‖(bT u:ℍ) - 1‖ ≤ 2 * ‖u - 1‖:=by
 by_cases hu:u = 0
 ·simp [hu,bT]
 let v:ℍ:=bT u
 have hv:‖v‖ = 1:=(c9 _).mp (bT u).property
 have hr:‖u‖ • v = u:=by
  simp [v,c1 hu,smul_smul,norm_ne_zero_iff.mpr hu]
 have hrad:‖u - v‖ = |‖u‖ - 1|:=by
  calc
   _ = ‖(‖u‖ - 1) • v‖:=by rw [sub_smul,hr,one_smul]
   _ = _:=by rw [norm_smul,hv,mul_one,Real.norm_eq_abs]
 have h:=abs_norm_sub_norm_le u (1:ℍ)
 rw [norm_one,← hrad,norm_sub_rev] at h
 exact (norm_sub_le_norm_sub_add_norm_sub v u 1).trans (by linarith)
end EilenbergGanea
namespace EilenbergGanea
open scoped Quaternion ContDiff
open Set
section SelectedEquations
variable {E:Type*} {m d:ℕ}
def kG (σ:Fin m ↪ E) (e:E):E ⊕ Fin m:=by
 classical
 exact if h:∃ i,σ i=e then .inr h.choose else .inl e
@[simp] theorem df6 (σ:Fin m ↪ E) (i:Fin m) :
    kG σ (σ i)=.inr i:=by
  classical
  have h:∃ j,σ j=σ i:=⟨i,rfl⟩
  simp only [kG,dif_pos h]
  exact congrArg Sum.inr (σ.injective h.choose_spec)
 theorem N7 (σ:Fin m ↪ E) (e:E) (he:∀ i,σ i ≠ e) :
    kG σ e=.inl e:=by
  classical
  simp [kG,he]
def jD (σ:Fin m ↪ E):FreeGroup E →* FreeGroup (E ⊕ Fin m):=
 FreeGroup.map (kG σ)
def iG (σ:Fin m ↪ E) (a:E -> a3) (x:Fin m -> a3) (e:E):a3:=
 Sum.elim a x (kG σ e)
@[simp] theorem dk0 (σ:Fin m ↪ E) (a:E -> a3)
    (x:Fin m -> a3) (i:Fin m):iG σ a x (σ i)=x i:=by
  simp [iG]
 theorem N8 (σ:Fin m ↪ E) (a:E -> a3) (x:Fin m -> a3)
    (e:E) (he:∀ i,σ i ≠ e):iG σ a x e=a e:=by
  rw [iG,N7 σ e he]
  rfl
 theorem x9 (σ:Fin m ↪ E) (a:E -> a3) (x:Fin m -> a3)
    (w:FreeGroup E) :
    FreeGroup.lift (Sum.elim a x) (jD σ w) =
      FreeGroup.lift (iG σ a x) w:=by
  have he:(FreeGroup.lift (Sum.elim a x)).comp (jD σ) =
      FreeGroup.lift (iG σ a x):=by
    apply FreeGroup.ext_hom
    intro e
    simp [jD,iG]
  exact congrArg (fun f:FreeGroup E →* a3=>f w) he
 theorem wX [DecidableEq E] (σ:Fin m ↪ E) (w:FreeGroup E) (j:Fin m) :
    dN (cO (jD σ w)) j=dN w (σ j):=by
  classical
  have he:(FreeGroup.lift (fun i:Fin m=>Multiplicative.ofAdd (if j=i then (1:ℤ) else 0))).comp
      (cO.comp (jD σ)) =
      FreeGroup.lift (fun e:E=>Multiplicative.ofAdd (if σ j=e then (1:ℤ) else 0)):=by
    apply FreeGroup.ext_hom
    intro e
    by_cases h:∃ i,σ i=e
    · obtain ⟨i,rfl⟩:=h
      simp [jD,cO,σ.injective.eq_iff]
    · have h':∀ i,σ i ≠ e:=by simpa only [not_exists] using h
      simp [jD,cO,N7 σ e h',h' j]
  exact congrArg (fun f:FreeGroup E →* Multiplicative ℤ=>(f w).toAdd) he
theorem Tv {J:Type*} [Fintype J] [DecidableEq E]
  (σ:Fin m ↪ E) (w:Fin m -> FreeGroup E) (ρ:J -> FreeGroup E)
  (a:ℝ -> E -> a3) (ha:∀ e,ContDiff ℝ ∞ (fun t=>(a t e:ℍ)))
  (ha0:∀ e,a 0 e=1)
  (hB:Matrix.det (fun i j=>dN (w i) (σ j)) ≠ 0)
  (δ:ℝ) (hδ:0 < δ)
  (hiso:∀ t ∈ Icc (0:ℝ) 1,∀ x:Fin m -> a3,
   (∀ i,FreeGroup.lift (iG σ (a t) x) (w i)=1) ->
   ‖(fun i=>(FreeGroup.lift (iG σ (a t) x) (ρ i):ℍ)) - 1‖ ≠ δ) :
  ∃ b:E -> a3,
   (∀ e,(∀ i,σ i ≠ e) -> b e=a 1 e) /\
   (∀ i,FreeGroup.lift b (w i)=1) /\
   ‖(fun i=>(FreeGroup.lift b (ρ i):ℍ)) - 1‖ < δ:=by
 have hb:(c8 (fun i=>cO (jD σ (w i)))).det ≠ 0:=by
  change (Matrix.det (fun i j=>dN (cO (jD σ (w i))) j)) ≠ 0
  simpa only [wX] using hB
 obtain ⟨x,hx,hρ⟩:=Tj
  (fun i=>jD σ (w i)) (fun i=>jD σ (ρ i)) a ha ha0 hb δ hδ
  (fun t ht x hx=>by
   simp only [dL,x9]
   apply hiso t ht x
   intro i
   have hi:=congrFun hx i
   simpa only [dL,x9,Pi.one_apply] using hi)
 refine ⟨iG σ (a 1) x,fun e he=>N8 σ _ x e he,?_,?_⟩
 ·intro i
  have hi:=congrFun hx i
  simpa only [dL,x9,Pi.one_apply] using hi
 ·simpa only [dL,x9] using hρ
end SelectedEquations
end EilenbergGanea
namespace EilenbergGanea
variable {Γ S H:Type*} [Group Γ] [Group H]
def lG (v:S -> Γ) (a:Γ -> S -> H) :
  FreeGroup S →* ((Γ -> H) ⋊[tZ Γ H] Γ):=
 FreeGroup.lift (fun s=>⟨fun g=>a g s,v s⟩)
def aD (v:S -> Γ):FreeGroup S →* Γ:=FreeGroup.lift v
def aR (v:S -> Γ) (a:Γ -> S -> H) (w:FreeGroup S) (g:Γ):H:=
  (lG v a w).left g
 theorem Lm (v:S -> Γ) (a:Γ -> S -> H) (w:FreeGroup S) :
    (lG v a w).right=aD v w:=by
  have he:(SemidirectProduct.rightHom:((Γ -> H) ⋊[tZ Γ H] Γ) →* Γ).comp
      (lG v a)=aD v:=by
    apply FreeGroup.ext_hom
    intro s
    simp [lG,aD]
  exact congrArg (fun f:FreeGroup S →* Γ=>f w) he
@[simp] theorem ds6 (v:S -> Γ) (a:Γ -> S -> H) (g:Γ) :
  aR v a 1 g=1:=by simp [aR]
@[simp] theorem f2 (v:S -> Γ) (a:Γ -> S -> H) (s:S) (g:Γ) :
    aR v a (FreeGroup.of s) g=a g s:=by simp [aR,lG]
 theorem d4 (v:S -> Γ) (a:Γ -> S -> H) (w z:FreeGroup S) (g:Γ) :
    aR v a (w*z) g=aR v a w g * aR v a z (g * aD v w):=by
  simp only [aR,map_mul,SemidirectProduct.mul_left,Pi.mul_apply,Lm]
  rfl
 theorem e5 (v:S -> Γ) (a:Γ -> S -> H) (w:FreeGroup S) (g:Γ) :
    aR v a w⁻¹ g=(aR v a w (g * (aD v w)⁻¹))⁻¹:=by
  simp only [aR,map_inv,SemidirectProduct.inv_left,Lm]
  rfl
 theorem p7 (v:S -> Γ) (a:Γ -> S -> H)
    (u r:FreeGroup S) (hr:aD v r=1) (g:Γ) :
    aR v a (u*r*u⁻¹) g=aR v a u g *
      aR v a r (g * aD v u) * (aR v a u g)⁻¹:=by
  rw [d4,d4,e5,map_mul,hr,mul_one]
  simp only [mul_inv_cancel_right]
theorem zS {D T:Type*} [Group D] {v:S → Γ} {u:T → D}
  (φ:FreeGroup S →* FreeGroup T) (q:Γ →* D)
  (h:∀ s,aD u (φ (FreeGroup.of s))=q (v s)) (w:FreeGroup S) :
  aD u (φ w)=q (aD v w):=by
 apply DFunLike.congr_fun (f:=(aD u).comp φ) (g:=q.comp (aD v))
 apply FreeGroup.ext_hom
 simpa [aD] using h
theorem o8 {D:Type*} [Group D] (v:S -> Γ) (q:Γ →* D) (w:FreeGroup S) :
  aD (fun s=>q (v s)) w=q (aD v w):=
 zS (.id _) q (by simp [aD]) w
/-- Transport a path along a word substitution and an equivariant vertex map.
It suffices to check the label square on individual edges. -/
theorem pL {T D K:Type*} [Group D] [Group K]
  {v:S → Γ} {u:T → D} {a:Γ → S → H} {b:D → T → K}
  (φ:FreeGroup S →* FreeGroup T) (q:Γ → D) (f:H →* K)
  (hv:∀ p w,q (p * aD v w)=q p * aD u (φ w))
  (he:∀ p s,f (a p s)=aR u b (φ (FreeGroup.of s)) (q p))
  (w:FreeGroup S) (g:Γ):f (aR v a w g)=aR u b (φ w) (q g):=by
 induction w using FreeGroup.induction_on generalizing g with
 | C1=>simp
 | of s=>simpa only [f2] using he g s
 | inv_of s ih=>
  have h:=hv g (FreeGroup.of s)⁻¹
  simp only [map_inv] at h
  simp only [map_inv,e5,ih,h]
 | mul w z hw hz=>simp only [map_mul,d4,hw,hz,hv]
def jP (v:S -> Γ) (w:FreeGroup S) (g:Γ):FreeGroup (Γ × S):=
 aR v (fun p s=>FreeGroup.of (p,s)) w g
theorem Ky (v:S -> Γ) (a:Γ -> S -> H) (w:FreeGroup S) (g:Γ) :
  FreeGroup.lift (fun i:Γ × S=>a i.1 i.2) (jP v w g) =
   aR v a w g:=
 pL (.id _) id _ (fun _ _=>rfl) (fun _ _=>by simp) w g
theorem Tw [TopologicalSpace H] [IsTopologicalGroup H]
  (v:S -> Γ) (w:FreeGroup S) (g:Γ) :
  Continuous (fun a:Γ -> S -> H=>aR v a w g):=by
 simp_rw [← Ky]
 obtain ⟨l,hl⟩:=Quot.exists_rep (jP v w g)
 change FreeGroup.mk l = jP v w g at hl
 simp_rw [← hl,FreeGroup.lift_mk]
 apply continuous_list_prod
 rintro ⟨⟨p,s⟩,b⟩ _
 cases b
 ·exact (continuous_apply_apply p s).inv
 ·exact continuous_apply_apply p s
theorem Tx (v:S -> Γ) (w:FreeGroup S) (g:Γ) :
  ∃ P:Finset Γ,∀ a b:Γ -> S -> H,
   (∀ p ∈ P,∀ s,a p s=b p s) -> aR v a w g=aR v b w g:=by
 classical
 obtain ⟨l,hl⟩:=Quot.exists_rep (jP v w g)
 change FreeGroup.mk l = jP v w g at hl
 refine ⟨(l.map (fun e=>e.1.1)).toFinset,fun a b h=>?_⟩
 simp only [← Ky,← hl,FreeGroup.lift_mk]
 congr 1
 apply List.map_congr_left
 intro e he
 rw [h e.1.1 (by simpa using List.mem_map_of_mem (f:=fun e:((Γ × S) × Bool)=>e.1.1) he) e.1.2]
theorem Tz {D:Type*} [Group D] (q:Γ →* D)
    (v:S -> Γ) (a:D -> S -> H) (w:FreeGroup S) (g:Γ) :
    aR v (fun p s=>a (q p) s) w g=aR (fun s=>q (v s)) a w (q g):=by
  exact pL (.id _) q (.id _) (fun p w=>by simp [o8]) (fun _ _=>by simp) w g
 theorem TA (v:S -> Γ) (a:Γ -> S -> H)
    (R:Set (FreeGroup S)) (hR:R ⊆ (aD v).ker)
    (hp:(aD v).ker=Subgroup.normalClosure R)
    (ha:∀ r ∈ R,∀ g,aR v a r g=1)
    (w:FreeGroup S) (hw:aD v w=1) (g:Γ):aR v a w g=1:=by
  have hrel:R ⊆ (lG v a).ker:=by
    intro r hr
    change lG v a r=1
    apply SemidirectProduct.ext
    · funext g
      exact ha r hr g
    · rw [Lm]
      exact hR hr
  have hle:Subgroup.normalClosure R <= (lG v a).ker:=
    Subgroup.normalClosure_le_normal hrel
  have he:lG v a w=1:=hle (by rw [<- hp]; exact hw)
  change (lG v a w).left g=1
  rw [he]
  rfl
 def aW (v:S -> Γ) (w:FreeGroup S) (g:Γ):(Γ × S) →₀ ℤ:=
  (aR v (fun p s=>Multiplicative.ofAdd (Finsupp.single (p,s) 1)) w g).toAdd
@[simp] theorem N9 (v:S -> Γ) (g:Γ):aW v 1 g=0:=by
 simp [aW]
@[simp] theorem Lq (v:S -> Γ) (s:S) (g:Γ) :
    aW v (FreeGroup.of s) g=Finsupp.single (g,s) 1:=by simp [aW]
 theorem d2 (v:S -> Γ) (w z:FreeGroup S) (g:Γ) :
    aW v (w*z) g=aW v w g + aW v z (g * aD v w):=by
  simp only [aW,d4,toAdd_mul]
 theorem f9 (v:S -> Γ) (w:FreeGroup S) (g:Γ) :
    aW v w⁻¹ g=-aW v w (g * (aD v w)⁻¹):=by
  simp only [aW,e5,toAdd_inv]
 theorem n5 (v:S -> Γ) (u r:FreeGroup S)
    (hr:aD v r=1) (g:Γ) :
    aW v (u*r*u⁻¹) g=aW v r (g * aD v u):=by
  simp only [aW,p7 v _ u r hr g,
    toAdd_mul,toAdd_inv]
  abel
variable {R:Type*}
abbrev qN (G I:Type*):=G × I × Bool
abbrev d1 (S R:Type*):=qN (FreeGroup S) R
def jX {G:Type*} [Group G] (b:G) (ε:Bool):G:=if ε then b else b⁻¹
def eO {G I:Type*} [Group G] (x:I -> G) (r:qN G I):G:=
 r.1 * jX (x r.2.1) r.2.2 * r.1⁻¹
abbrev cW (r:R -> FreeGroup S):=eO r
 def gT (v:S -> Γ) (f:d1 S R) (g:Γ):(Γ × R) →₀ ℤ:=
  Finsupp.single (g * aD v f.1,f.2.1) (if f.2.2 then 1 else -1)
 def aO (v:S -> Γ) (r:R -> FreeGroup S) :
    ((Γ × R) →₀ ℤ) →ₗ[ℤ] ((Γ × S) →₀ ℤ):=
  Finsupp.linearCombination ℤ (fun i=>aW v (r i.2) i.1)
 theorem TD (v:S -> Γ) (r:R -> FreeGroup S)
    (hr:∀ i,aD v (r i)=1) (f:d1 S R) :
    aD v (cW r f)=1:=by
  dsimp only [cW,eO,jX]
  split_ifs <;> simp [hr]
def gC (v:S -> Γ) (a:Γ -> S -> H)
  (f:d1 S R) (g:Γ):qN H (Γ × R):=
 (aR v a f.1 g,(g * aD v f.1,f.2.1),f.2.2)
theorem TJ (v:S -> Γ) (a:Γ -> S -> H)
    (r:R -> FreeGroup S) (hr:∀ i,aD v (r i)=1)
    (f:d1 S R) (g:Γ) :
    eO (fun i:Γ × R=>aR v a (r i.2) i.1)
      (gC v a f g)=aR v a (cW r f) g:=by
  rcases f with ⟨u,i,σ⟩
  cases σ <;>
    simp [eO,gC,jX,cW,
      p7,hr,e5]
theorem Ls (v:S -> Γ) (a:Γ -> S -> H)
    (r:R -> FreeGroup S) (hr:∀ i,aD v (r i)=1)
    (l:List (d1 S R)) (g:Γ) :
    ((l.map (fun f=>gC v a f g)).map
      (eO (fun i:Γ × R=>aR v a (r i.2) i.1))).prod =
      aR v a (l.map (cW r)).prod g:=by
  induction l with
  | nil=>simp
  | cons f l ih=>
      simp only [List.map_cons,List.prod_cons,d4,
        TD v r hr,mul_one,TJ v a r hr,ih]
 theorem TK (v:S -> Γ) (r:R -> FreeGroup S)
    (hr:∀ i,aD v (r i)=1) (l:List (d1 S R)) (g:Γ) :
    aW v (l.map (cW r)).prod g =
      aO v r (l.map (fun f=>gT v f g)).sum:=by
  rw [aW,← Ls v _ r hr,toAdd_list_sum,map_list_sum]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro f _
  cases h:f.2.2 <;> simp [Function.comp_def,eO,gC,
    jX,gT,aO,aW,h]
 theorem TQ (v:S -> Γ) (r:R -> FreeGroup S)
    (hr:∀ i,aD v (r i)=1) (hinj:Function.Injective (aO v r))
    (z:FreeGroup S) (ρ:R) (hchain:aW v z 1=aW v (r ρ) 1)
    (l:List (d1 S R)) (he:z=(l.map (cW r)).prod) :
    (l.map (fun f=>gT v f 1)).sum=Finsupp.single (1,ρ) 1:=by
  apply hinj
  rw [<- TK v r hr,<- he,hchain]
  simp [aO]
end EilenbergGanea
namespace EilenbergGanea
variable {Γ S H:Type*} [Group Γ] [Group H]
section CompactLabeling
variable {T I:Type*}
 def dQ (a:Γ -> S -> H) (b:Γ -> T -> H):Γ -> S ⊕ T -> H:=
  fun g=>Sum.elim (a g) (b g)
 omit [Group Γ] [Group H] in
 theorem TU [TopologicalSpace H] (a:Γ -> S -> H) :
    Continuous (fun b:Γ -> T -> H=>dQ a b):=by
  apply continuous_pi
  intro g
  apply continuous_pi
  intro s
  cases s with
  | inl s=>exact continuous_const
  | inr t=>exact continuous_apply_apply g t
 theorem TW {D:Type*} [Group D] (q:Γ →* D)
    (P:Finset Γ) (hq:Set.InjOn q (P:Set Γ)) (a:Γ -> S -> H)
    (Allowed:H -> Prop) (h1:Allowed 1) (ha:∀ g s,Allowed (a g s)) :
    ∃ aF:D -> S -> H,(∀ d s,Allowed (aF d s)) /\ ∀ p ∈ P,∀ s,aF (q p) s=a p s:=by
  classical
  let aF:D -> S -> H:=fun d s=>if hd:∃ p ∈ P,q p=d then a hd.choose s else 1
  refine ⟨aF,?_,?_⟩
  · intro d s
    dsimp [aF]
    split_ifs
    · exact ha _ _
    · exact h1
  · intro p hp s
    have he:∃ p' ∈ P,q p'=q p:=⟨p,hp,rfl⟩
    simp only [aF,dif_pos he]
    have heq:he.choose=p:=hq he.choose_spec.1 hp he.choose_spec.2
    rw [heq]
 theorem oA [Group.ResiduallyFinite Γ]
    [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
    (v:S ⊕ T -> Γ) (a:Γ -> S -> H) (w:I -> FreeGroup (S ⊕ T)) (g:I -> Γ)
    (K:I -> Set H) (hK:∀ i,IsClosed (K i))
    (Allowed:H -> Prop) (h1:Allowed 1) (ha:∀ g s,Allowed (a g s))
    (hsolve:∀ (N:FiniteIndexNormalSubgroup Γ) (J:Finset I)
      (aF:(Γ ⧸ N.toSubgroup) -> S -> H),(∀ d s,Allowed (aF d s)) ->
      ∃ bF:(Γ ⧸ N.toSubgroup) -> T -> H,∀ i ∈ J,∀ d,
        aR (fun s=>QuotientGroup.mk' N.toSubgroup (v s))
          (dQ aF bF) (w i) d ∈ K i) :
    ∃ b:Γ -> T -> H,∀ i,aR v (dQ a b) (w i) (g i) ∈ K i:=by
  classical
  let C:I -> Set (Γ -> T -> H):=fun i=>
    {b | aR v (dQ a b) (w i) (g i) ∈ K i}
  have hc:∀ i,IsClosed (C i):=fun i=>
    (hK i).preimage ((Tw v (w i) (g i)).comp (TU a))
  have hf:∀ J:Finset I,(⋂ i ∈ J,C i).Nonempty:=by
    intro J
    choose P hP using (fun i:I=>Tx (H:=H) v (w i) (g i))
    let V:=J.biUnion P
    obtain ⟨N,hN⟩:=x1 V
    let q:=QuotientGroup.mk' N.toSubgroup
    obtain ⟨aF,haF,heF⟩:=TW q V hN a Allowed h1 ha
    obtain ⟨bF,hbF⟩:=hsolve N J aF haF
    refine ⟨fun p t=>bF (q p) t,?_⟩
    simp only [Set.mem_iInter]
    intro i hi
    change aR v (dQ a (fun p t=>bF (q p) t)) (w i) (g i) ∈ K i
    have he:aR v (dQ a (fun p t=>bF (q p) t)) (w i) (g i) =
        aR v (fun p s=>dQ aF bF (q p) s) (w i) (g i):=by
      apply hP i
      intro p hp s
      cases s with
      | inl s=>exact (heF p (Finset.mem_biUnion.mpr ⟨i,hi,hp⟩) s).symm
      | inr t=>rfl
    rw [he,Tz]
    exact hbF i hi (q (g i))
  obtain ⟨b,hb⟩:=CompactSpace.iInter_nonempty hc hf
  exact ⟨b,fun i=>Set.mem_iInter.mp hb i⟩
end CompactLabeling
end EilenbergGanea
open scoped Quaternion
namespace EilenbergGanea
theorem Kz (a:a3):‖(a:ℍ)‖=1:=by
 have h:star (a:ℍ) * (a:ℍ)=1:=a.property.1
 have hn:=congrArg norm h
 simp only [norm_mul,norm_star,norm_one] at hn
 nlinarith [norm_nonneg (a:ℍ)]
theorem vW (a b:a3) :
    ‖((a*b:a3):ℍ) - 1‖ <= ‖(a:ℍ) - 1‖ + ‖(b:ℍ) - 1‖:=by
  have he:((a*b:a3):ℍ) - 1=((a:ℍ) - 1) * (b:ℍ) + ((b:ℍ) - 1):=by
    change (a:ℍ) * (b:ℍ) - 1=_
    noncomm_ring
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [norm_mul,Kz,mul_one])
 theorem tD (a b:ℍ) :
    ‖a * b - b * a‖ <= 2 * ‖a - 1‖ * ‖b - 1‖:=by
  have he:a * b - b * a=(a - 1) * (b - 1) - (b - 1) * (a - 1):=by noncomm_ring
  rw [he]
  calc
    _ <= ‖(a - 1) * (b - 1)‖ + ‖(b - 1) * (a - 1)‖:=norm_sub_le _ _
    _=_:=by rw [norm_mul,norm_mul]; ring
 theorem TY (a b:a3) :
    ‖((a * b * a⁻¹:a3):ℍ) - (b:ℍ)‖ <= 2 * ‖(a:ℍ) - 1‖ * ‖(b:ℍ) - 1‖:=by
  have he:((a * b * a⁻¹:a3):ℍ) - (b:ℍ) =
      ((a:ℍ) * (b:ℍ) - (b:ℍ) * (a:ℍ)) * ((a⁻¹:a3):ℍ):=by
    change (a:ℍ) * (b:ℍ) * star (a:ℍ) - (b:ℍ)=_
    change _=((a:ℍ) * (b:ℍ) - (b:ℍ) * (a:ℍ)) * star (a:ℍ)
    rw [sub_mul,mul_assoc (b:ℍ),a.property.2,mul_one]
  rw [he,norm_mul,Kz,mul_one]
  exact tD _ _
 theorem q1 (b:a3):‖((b⁻¹:a3):ℍ) - 1‖=‖(b:ℍ) - 1‖:=by
  change ‖star (b:ℍ) - 1‖=_
  calc
    _=‖star ((b:ℍ) - 1)‖:=by rw [star_sub,star_one]
    _=_:=norm_star _
 theorem vH (b:a3) :
    ‖((b⁻¹:a3):ℍ) - 1 + ((b:ℍ) - 1)‖ <= ‖(b:ℍ) - 1‖^2:=by
  have he:((b⁻¹:a3):ℍ) - 1 + ((b:ℍ) - 1) =
      -((((b⁻¹:a3):ℍ) - 1) * ((b:ℍ) - 1)):=by
    have hb:((b⁻¹:a3):ℍ) * (b:ℍ)=1:=b.property.1
    noncomm_ring [hb]
  rw [he,norm_neg,norm_mul,q1,pow_two]
theorem T8 (a b:a3) :
  ‖((a * b * a⁻¹:a3):ℍ) - 1‖=‖(b:ℍ) - 1‖:=by
 have he:((a * b * a⁻¹:a3):ℍ) - 1 =
   (a:ℍ) * ((b:ℍ) - 1) * star (a:ℍ):=by
  change (a:ℍ) * (b:ℍ) * star (a:ℍ) - 1=_
  rw [mul_sub,sub_mul,mul_one,a.property.2]
 rw [he,norm_mul,norm_mul,norm_star,Kz,one_mul,mul_one]
def jE (b:a3) (ε:Bool):ℍ:=if ε then (b:ℍ) - 1 else -((b:ℍ) - 1)
 theorem Oa (b:a3) (ε:Bool) :
    ‖((jX b ε:a3):ℍ) - 1‖=‖(b:ℍ) - 1‖:=by
  cases ε <;> simp [jX,q1]
 theorem T9 (b:a3) (ε:Bool) :
    ‖((jX b ε:a3):ℍ) - 1 - jE b ε‖ <= ‖(b:ℍ) - 1‖^2:=by
  cases ε with
  | false=>
      change ‖((b⁻¹:a3):ℍ) - 1 - (-((b:ℍ) - 1))‖ <= _
      simpa only [sub_neg_eq_add] using vH b
  | true=>simp [jX,jE]
abbrev Ly (I:Type*):=qN a3 I
def kD {I:Type*} (l:List (Ly I)):I →₀ ℤ:=
  (l.map (fun r=>Finsupp.single r.2.1 (if r.2.2 then 1 else -1))).sum
 theorem Ud {I:Type*} (l:List (Ly I)) (x:I -> a3) :
    (l.map (fun r=>jE (x r.2.1) r.2.2)).sum =
      Finsupp.linearCombination ℤ (fun i=>(x i:ℍ) - 1) (kD l):=by
  simp only [kD,map_list_sum,List.map_map]
  congr 1
  apply List.map_congr_left
  intro r _
  cases h:r.2.2 <;> simp [jE,h]
/-- Appending one evaluated factor adds its signed displacement, up to a
cross term controlled by the distance already travelled by the prefix. -/
theorem uY {I:Type*} (x:I -> a3) (h A:ℝ) (hh:0 ≤ h) (hA:0 ≤ A)
    (l:List (Ly I)) (hb:∀ r ∈ l,‖(x r.2.1:ℍ) - 1‖ ≤ h)
    (ha:∀ r ∈ l,‖(r.1:ℍ) - 1‖ ≤ A) :
    let P:=((l.map (eO x)).prod:ℍ)
    let S:=(l.map (fun r=>jE (x r.2.1) r.2.2)).sum
    ‖P - 1‖ ≤ l.length*h ∧ ‖P - 1 - S‖ ≤ (l.length:ℝ)^2*h^2 + l.length*(2*A*h+h^2):=by
  induction l using List.reverseRecOn with
  | nil=>simp
  | append_singleton l r ih=>
    obtain ⟨hp,hs⟩:=ih (fun i hi=>hb i (by simp [hi])) (fun i hi=>ha i (by simp [hi]))
    let p:=(l.map (eO x)).prod
    let u:=eO x r
    let b:=x r.2.1
    let t:=jX b r.2.2
    let v:=jE b r.2.2
    have hb':‖(b:ℍ)-1‖ ≤ h:=hb r (by simp)
    have hu:‖(u:ℍ)-1‖ ≤ h:=((T8 _ _).trans (Oa _ _)).le.trans hb'
    have he:‖(u:ℍ)-1-v‖ ≤ 2*A*h+h^2:=calc
      _ ≤ ‖(u:ℍ)-(t:ℍ)‖ + ‖(t:ℍ)-1-v‖:=by
        simpa only [sub_sub_sub_cancel_right] using norm_sub_le_norm_sub_add_norm_sub ((u:ℍ)-1) ((t:ℍ)-1) v
      _ ≤ _:=by
        have hc:=TY r.1 t
        rw [show ‖(t:ℍ)-1‖ = ‖(b:ℍ)-1‖ from Oa _ _] at hc
        exact add_le_add (hc.trans (by gcongr; exact ha r (by simp))) ((T9 b _).trans (by gcongr))
    simp only [List.map_append,List.map_singleton,List.prod_append,List.prod_singleton,
      List.sum_append,List.sum_singleton,List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
    constructor
    · exact (vW p u).trans ((add_le_add hp hu).trans_eq (by ring))
    · let s:=(l.map (fun r=>jE (x r.2.1) r.2.2)).sum
      change ‖(p:ℍ)*(u:ℍ)-1-(s+v)‖ ≤ _
      rw [show (p:ℍ)*(u:ℍ)-1-(s+v) = ((p:ℍ)-1-s) + (((p:ℍ)-1)*((u:ℍ)-1) + ((u:ℍ)-1-v)) by noncomm_ring]
      apply (norm_add_le _ _).trans
      have cross:‖((p:ℍ)-1)*((u:ℍ)-1)‖ ≤ l.length*h*h:=by
        rw [norm_mul]; exact mul_le_mul hp hu (norm_nonneg _) (by positivity)
      exact (add_le_add hs ((norm_add_le _ _).trans (add_le_add cross he))).trans
        (by nlinarith [mul_nonneg (Nat.cast_nonneg (α:=ℝ) l.length) (sq_nonneg h),sq_nonneg h])
 theorem Ue (C:ℝ) (hC:1 <= C) :
    ∃ δ η:ℝ,0 < δ /\ δ < 1 /\ 0 < η /\ η < 1 /\
      C * (δ + η) < 1/2 /\ C * η < δ/2:=by
  have hc:0 < C:=by linarith
  let δ:=1 / (8*C)
  let η:=δ / (8*C)
  have hd:0 < δ:=by dsimp [δ]; positivity
  have hd1:δ < 1:=by dsimp [δ]; apply (div_lt_iff₀ (by positivity)).mpr; linarith
  have he:0 < η:=by dsimp [η]; positivity
  have heδ:η < δ:=by dsimp [η]; apply (div_lt_iff₀ (by positivity)).mpr; nlinarith
  have hcd:C * δ=1/8:=by dsimp [δ]; field_simp
  have hce:C * η=δ/8:=by dsimp [η]; field_simp
  refine ⟨δ,η,hd,hd1,he,heδ.trans hd1,?_,?_⟩
  · rw [mul_add,hcd,hce]; linarith
  · rw [hce]; linarith
end EilenbergGanea
end
noncomputable section
universe u
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea
section NaturalPath
variable {Γ S H K:Type*} [Group Γ] [Group H] [Group K]
theorem Uh (v:S -> Γ) (w:FreeGroup S) (g:Γ) :
  FreeGroup.lift (fun i:Γ × S=>Multiplicative.ofAdd (Finsupp.single i (1:ℤ)))
   (jP v w g)=Multiplicative.ofAdd (aW v w g):=by
 exact Ky v (fun p s=>Multiplicative.ofAdd (Finsupp.single (p,s) (1:ℤ))) w g
end NaturalPath
section NormalExpressions
variable {S R:Type*}
def oB (f:d1 S R):d1 S R:=
 (f.1,f.2.1,!f.2.2)
theorem Uj (r:R -> FreeGroup S) (f:d1 S R) :
  cW r (oB f)=(cW r f)⁻¹:=by
 rcases f with ⟨u,i,ε⟩
 cases ε <;> simp [cW,eO,jX,oB,mul_assoc]
theorem Ob (r:R -> FreeGroup S) {w:FreeGroup S}
  (hw:w ∈ Subgroup.normalClosure (Set.range r)) :
  ∃ l:List (d1 S R),w=(l.map (cW r)).prod:=by
 change w ∈ Subgroup.closure (Group.conjugatesOfSet (Set.range r)) at hw
 induction hw using Subgroup.closure_induction with
 | mem x hx=>
   obtain ⟨y,⟨i,rfl⟩,hy⟩:=Group.mem_conjugatesOfSet_iff.mp hx
   obtain ⟨u,hu⟩:=isConj_iff.mp hy
   refine ⟨[(u,i,true)],?_⟩
   simpa [cW,eO,jX] using hu.symm
 | one=>exact ⟨[],by simp⟩
 | mul x y hx hy ihx ihy=>
   obtain ⟨l,rfl⟩:=ihx
   obtain ⟨k,rfl⟩:=ihy
   exact ⟨l ++ k,by simp⟩
 | inv x hx ih=>
   obtain ⟨l,rfl⟩:=ih
   refine ⟨(l.map oB).reverse,?_⟩
   simp only [List.map_reverse,List.prod_inv_reverse,List.map_map]
   congr 2
   apply List.map_congr_left
   intro f _
   exact (Uj r f).symm
end NormalExpressions
section WordNorm
open scoped Quaternion
variable {Γ S:Type*} [Group Γ]
private theorem CY {R:Type*} (A:S → Finset R) (k:S → ℕ) (w:FreeGroup S) :
  ∃ (B:Finset R) (n:ℕ),∀ {D:Type u} [Group D] (v:S → D) (a:D → S → a3) (δ:ℝ),
   (∀ s,A s ⊆ B → ∀ p,‖(a p s:ℍ)-1‖ ≤ k s * δ) →
   ∀ p,‖((aR v a w p:a3):ℍ)-1‖ ≤ n * δ:=by
 classical
 induction w using FreeGroup.induction_on with
 | C1=>exact ⟨∅,0,fun _ _ _ _ _=>by simp⟩
 | of s=>exact ⟨A s,k s,fun _ _ _ ha p=>by simpa using ha s Subset.rfl p⟩
 | inv_of s ih=>
  obtain ⟨B,n,hn⟩:=ih
  exact ⟨B,n,fun v a δ ha p=>by rw [e5,q1]; exact hn v a δ ha _⟩
 | mul w z hw hz=>
  obtain ⟨B,n,hn⟩:=hw
  obtain ⟨C,m,hm⟩:=hz
  refine ⟨B ∪ C,n+m,fun v a δ ha p=>?_⟩
  rw [d4,Nat.cast_add,add_mul]
  exact (vW _ _).trans (add_le_add
   (hn v a δ (fun s hs=>ha s (hs.trans Finset.subset_union_left)) _)
   (hm v a δ (fun s hs=>ha s (hs.trans Finset.subset_union_right)) _))
end WordNorm
section EvaluatedNormalExpression
open scoped Quaternion
variable {Γ D S R:Type*} [Group Γ] [Group D]
theorem Uk (v:S -> Γ) (q:Γ →* D)
  (a:D -> S -> a3) (l:List (d1 S R)) (ρ:R)
  (hc:(l.map (fun f=>gT v f 1)).sum=Finsupp.single (1,ρ) 1)
  (g:D) :
  kD (l.map (fun f=>gC (fun s=>q (v s)) a f g)) =
   Finsupp.single (g,ρ) 1:=by
 let T:((Γ × R) →₀ ℤ) →ₗ[ℤ] ((D × R) →₀ ℤ):=
  Finsupp.lmapDomain ℤ ℤ (fun i=>(g * q i.1,i.2))
 have hs:kD
   (l.map (fun f=>gC (fun s=>q (v s)) a f g)) =
   T (l.map (fun f=>gT v f 1)).sum:=by
  simp only [kD,List.map_map,map_list_sum]
  congr 1
  apply List.map_congr_left
  intro f _
  simp [T,gC,gT,o8]
 rw [hs,hc]
 simp [T]
theorem Um (v:S -> Γ) (q:Γ →* D)
    (a:D -> S -> a3) (r:R -> FreeGroup S)
    (hr:∀ i,aD v (r i)=1) (z:FreeGroup S)
    (l:List (d1 S R)) (he:z=(l.map (cW r)).prod)
    (ρ:R) (hc:(l.map (fun f=>gT v f 1)).sum =
      Finsupp.single (1,ρ) 1)
    (h ε K:ℝ) (hh:0 <= h) (hε:0 <= ε) (hK:0 <= K)
    (hb:∀ f ∈ l,∀ g,‖((aR (fun s=>q (v s)) a (r f.2.1) g:a3):ℍ) - 1‖ <= h)
    (ha:∀ f ∈ l,∀ g,‖((aR (fun s=>q (v s)) a f.1 g:a3):ℍ) - 1‖ <= K * (ε+h))
    (g:D) :
    ‖((aR (fun s=>q (v s)) a z g:a3):ℍ) -
      ((aR (fun s=>q (v s)) a (r ρ) g:a3):ℍ)‖ <=
      ((l.length:ℝ)^2 + l.length + 2*l.length*K) * (ε+h)*h:=by
  let v':=fun s=>q (v s)
  let L:=l.map (fun f=>gC v' a f g)
  let x:=fun i:D × R=>aR v' a (r i.2) i.1
  have hp:=(uY x h (K*(ε+h)) hh (by positivity) L
    (by intro f hf; obtain ⟨b,hb',rfl⟩:=List.mem_map.mp hf; exact hb b hb' _)
    (by intro f hf; obtain ⟨b,hb',rfl⟩:=List.mem_map.mp hf; exact ha b hb' _)).2
  have hz:=Ls v' a r (fun i=>by simp [v',o8,hr]) l g
  rw [← he] at hz
  rw [Ud,Uk v q a l ρ hc g,Finsupp.linearCombination_single,one_smul,hz,sub_sub_sub_cancel_right] at hp
  simp only [L,List.length_map] at hp
  exact hp.trans (by nlinarith [mul_nonneg (mul_nonneg (add_nonneg (sq_nonneg (l.length:ℝ))
    (Nat.cast_nonneg (α:=ℝ) l.length)) hε) hh])
end EvaluatedNormalExpression
open scoped Quaternion
section NormalProductSize
variable {Γ S R:Type*} [Group Γ]
theorem Uq (v:S -> Γ) (a:Γ -> S -> a3)
  (r:R -> FreeGroup S) (hr:∀ i,aD v (r i)=1)
  (l:List (d1 S R)) (h:ℝ) (hh:0 ≤ h)
  (hb:∀ f ∈ l,∀ g,‖((aR v a (r f.2.1) g:a3):ℍ) - 1‖ <= h)
  (g:Γ) :
  ‖((aR v a (l.map (cW r)).prod g:a3):ℍ) - 1‖ <= l.length * h:=by
 rw [← Ls v a r hr]
 apply (uY _ h 2 hh (by norm_num) _ ?_ ?_).1.trans_eq
 ·simp
 ·intro f hf
  obtain ⟨b,hb',rfl⟩:=List.mem_map.mp hf
  exact hb b hb' _
 ·intro f _
  exact (norm_sub_le _ _).trans (by norm_num [Kz])
end NormalProductSize
end EilenbergGanea
namespace EilenbergGanea
open scoped Quaternion
section FiniteControl
variable {S T H:Type*} [Group H]
 theorem KD {Γ:Type*} [Group Γ] (v:T → Γ) (f:S → T) (w:FreeGroup S) :
    aD v (FreeGroup.map f w)=aD (fun s=>v (f s)) w:=
  zS _ (.id _) (by simp [aD]) w
 theorem r4 {Γ:Type*} [Group Γ]
    (f:S -> T) (v:T -> Γ) (a:Γ -> T -> H) (w:FreeGroup S) (g:Γ) :
    aR v a (FreeGroup.map f w) g =
      aR (v ∘ f) (fun p s=>a p (f s)) w g:=by
  exact (pL (FreeGroup.map f) id (.id _) (by simp [KD,Function.comp_def]) (by simp) w g).symm
end FiniteControl
end EilenbergGanea
namespace EilenbergGanea
open scoped Quaternion BigOperators
section UniformComparison
variable {Γ S T Z R:Type*} [Group Γ] [Fintype Z]
def oC (v:S ⊕ T → Γ) (b:Γ → S ⊕ T → a3)
  (r:Z ⊕ R → FreeGroup (S ⊕ T)):Γ × Z → ℍ:=
 (fun p=>(aR (H:=a3) v b (r (.inl p.2)) p.1:ℍ)) - 1
theorem Ur
  (v:S ⊕ T -> Γ) (r:Z ⊕ R -> FreeGroup (S ⊕ T))
  (hr:∀ i,aD v (r i)=1) (z:Z -> FreeGroup S)
  (lz:Z -> List (d1 (S ⊕ T) (Z ⊕ R)))
  (lt:T -> List (d1 (S ⊕ T) (Z ⊕ R)))
  (hz:∀ i,FreeGroup.map Sum.inl (z i)=((lz i).map (cW r)).prod)
  (ht:∀ t,FreeGroup.of (Sum.inr t)=((lt t).map (cW r)).prod)
  (hc:∀ i,((lz i).map (fun f=>gT v f 1)).sum =
   Finsupp.single (1,Sum.inl i) 1) :
  ∃ (A:Finset R) (C:ℝ),1 <= C /\
   ∀ {F:Type u} [Group F] (q:Γ →* F) (a:F -> S ⊕ T -> a3)
    (ε h:ℝ),0 <= ε -> 0 <= h ->
   (∀ g s,‖(a g (.inl s):ℍ) - 1‖ <= ε) ->
   (∀ i ∈ A,∀ g,aR (fun s=>q (v s)) a (r (.inr i)) g=1) ->
   (∀ i g,‖((aR (fun s=>q (v s)) a (r (.inl i)) g:a3):ℍ) - 1‖ <= h) ->
   ∀ i g,‖oC (fun s=>q (v s)) a r (g,i)‖ ≤ C*(ε+h)*h +
    min ‖(aR (H:=a3) (fun s=>q (v s)) a (FreeGroup.map Sum.inl (z i)) g:ℍ)-1‖ (C*ε):=by
 classical
 let supp (l:List (d1 (S ⊕ T) (Z ⊕ R))):=(l.toFinset.image (fun f=>f.2.1)).toRight
 let A:S ⊕ T → Finset R:=Sum.elim (fun _=>∅) (fun t=>supp (lt t))
 let k:S ⊕ T → ℕ:=Sum.elim (fun _=>1) (fun t=>(lt t).length)
 choose B n hn using CY.{u,_,_} A k
 choose Bz m hm using CY.{u,_,_} (fun _:S=>(∅ : Finset R)) (fun _=>1)
 let L:=Finset.univ.biUnion fun i=>(lz i).toFinset
 let U:=(Finset.univ.biUnion fun i=>supp (lz i)) ∪ L.biUnion (fun f=>B f.1)
 let K:=L.sup fun f=>n f.1
 let c (i:Z):=(lz i).length^2 + (lz i).length + 2*(lz i).length*K + m (z i)
 let C:=Finset.univ.sup c + 1
 refine ⟨U,C,by exact_mod_cast Nat.succ_pos _,?_⟩
 intro F _ q a ε h hε hh ha ho hd i g
 let v':=fun s=>q (v s)
 have used (l) (hl:supp l ⊆ U) (f) (hf:f ∈ l) (p:F) :
   ‖((aR v' a (r f.2.1) p:a3):ℍ)-1‖ ≤ h:=by
  cases e:f.2.1 with
  | inl j=>exact hd j p
  | inr j=>rw [ho j (hl (Finset.mem_toRight.mpr (Finset.mem_image.mpr ⟨f,List.mem_toFinset.mpr hf,e⟩))) p]; simpa using hh
 have hc':c i ≤ C:=(Finset.le_sup (f:=c) (Finset.mem_univ i)).trans (Nat.le_succ _)
 let x:ℍ:=aR (H:=a3) v' a (r (.inl i)) g
 let y:ℍ:=aR (H:=a3) v' a (FreeGroup.map Sum.inl (z i)) g
 apply (norm_sub_le_norm_sub_add_norm_sub x y 1).trans (add_le_add ?_ (le_min le_rfl ?_))
 ·rw [norm_sub_rev x y]
  apply (Um v q a r hr _ _ (hz i) _ (hc i) h ε K hh hε (by positivity)
   (used _ ((Finset.subset_biUnion_of_mem (fun j=>supp (lz j)) (Finset.mem_univ i)).trans Finset.subset_union_left)) ?_ g).trans
  ·apply mul_le_mul_of_nonneg_right _ hh
   apply mul_le_mul_of_nonneg_right _ (add_nonneg hε hh)
   exact_mod_cast (show (lz i).length^2 + (lz i).length + 2*(lz i).length*K ≤ C by dsimp [c] at hc'; omega)
  ·intro f hf p
   have hfL:f ∈ L:=Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,List.mem_toFinset.mpr hf⟩
   apply (hn f.1 v' a (ε+h) ?_ p).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.le_sup (f:=fun f=>n f.1) hfL) (add_nonneg hε hh))
   intro s hs b
   cases s with
   | inl s=>simpa [k] using (ha b s).trans (le_add_of_nonneg_right hh)
   | inr t=>
    have hb:=Uq v' a r (fun j=>by simp [v',o8,hr]) (lt t) h hh
     (used _ ((hs.trans (Finset.subset_biUnion_of_mem (fun f=>B f.1) hfL)).trans Finset.subset_union_right)) b
    rw [← ht t,f2] at hb
    exact hb.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hε) (by positivity))
 ·dsimp only [y]
  rw [r4]
  apply (hm (z i) _ (fun p s=>a p (.inl s)) ε (fun s _ p=>by simpa using ha p s) g).trans
  apply mul_le_mul_of_nonneg_right _ hε
  exact_mod_cast (show m (z i) ≤ C by dsimp [c] at hc'; omega)
end UniformComparison
end EilenbergGanea
namespace EilenbergGanea
section QuotientChains
variable {Γ F R S T:Type*} [Group Γ] [Group F]
abbrev aE (Γ S:Type*):=(Γ × S) →₀ ℤ
def aZ (g:Γ):aE Γ S →ₗ[ℤ] aE Γ S:=
 Finsupp.lmapDomain ℤ ℤ (fun i=>(g*i.1,i.2))
def dG (q:Γ →* F):aE Γ S →ₗ[ℤ] aE F S:=
 Finsupp.lmapDomain ℤ ℤ (fun i=>(q i.1,i.2))
@[simp] theorem j8 (g h:Γ) (s:S) (n:ℤ) :
  aZ g (Finsupp.single (h,s) n)=Finsupp.single (g*h,s) n:=by
 simp [aZ]
@[simp] theorem Ut (q:Γ →* F) (g:Γ) (s:S) (n:ℤ) :
  dG q (Finsupp.single (g,s) n)=Finsupp.single (q g,s) n:=by
 simp [dG]
theorem Uv (q:Γ →* F) (g:Γ) (c:aE Γ S) :
  dG q (aZ g c)=aZ (q g) (dG q c):=by
 have he:(dG q).comp (aZ g) =
   ((aZ (q g)).comp (dG q):aE Γ S →ₗ[ℤ] _):=by
  apply Finsupp.lhom_ext
  rintro ⟨p,s⟩ n
  simp
 exact LinearMap.congr_fun he c
def b8 (A:aE Γ R →ₗ[ℤ] aE Γ S):Prop:=
 ∀ g c,A (aZ g c)=aZ g (A c)
def m6 (q:Γ →* F) (A:aE Γ R →ₗ[ℤ] aE Γ S) :
  aE F R →ₗ[ℤ] aE F S:=
 Finsupp.linearCombination ℤ (fun i=>
  aZ i.1 (dG q (A (Finsupp.single (1,i.2) 1))))
@[simp] theorem p4 (q:Γ →* F)
  (A:aE Γ R →ₗ[ℤ] aE Γ S) (f:F) (r:R) (n:ℤ) :
  m6 q A (Finsupp.single (f,r) n) =
   n • aZ f (dG q (A (Finsupp.single (1,r) 1))):=by
 simp [m6]
theorem Uw (q:Γ →* F)
  (A:aE Γ R →ₗ[ℤ] aE Γ S) (hA:b8 A)
  (c:aE Γ R) :
  m6 q A (dG q c)=dG q (A c):=by
 have he:(m6 q A).comp (dG q)=(dG q).comp A:=by
  apply Finsupp.lhom_ext
  rintro ⟨g,r⟩ n
  have hb:Finsupp.single (g,r) n =
    n • aZ g (Finsupp.single (1,r) (1:ℤ)):=by simp
  simp only [LinearMap.comp_apply,Ut,p4]
  rw [hb,map_smul,map_smul,hA,Uv]
 exact LinearMap.congr_fun he c
theorem b8.symm (A:aE Γ R ≃ₗ[ℤ] aE Γ S)
  (hA:b8 A.toLinearMap):b8 A.symm.toLinearMap:=by
 intro g c
 apply A.injective
 simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
 simpa only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply] using (hA g (A.symm c)).symm
end QuotientChains
open scoped BigOperators
theorem oH {I S:Type*} [Fintype I] [DecidableEq I]
  (v:I -> S →₀ ℤ) (B:(S →₀ ℤ) →ₗ[ℤ] (I -> ℤ))
  (hB:∀ i,B (v i)=Pi.single i 1) :
  ∃ e:I ↪ S,Matrix.det (fun i j=>v i (e j)) ≠ 0:=by
 classical
 let b (p:S):=B (Finsupp.single p 1)
 let w (p:S) (j:I):=v j p
 have trunc (j:I):∀ᶠ P:Finset S in Filter.atTop,
   ∑ p ∈ P,v j p • b p=Pi.single j 1:=by
  filter_upwards [Filter.eventually_ge_atTop (v j).support] with P hP
  rw [← Finsupp.sum_of_support_subset (v j) hP (fun p n=>n • b p) (by simp)]
  rw [← hB]
  conv_rhs=>rw [← Finsupp.sum_single (v j),Finsupp.sum,map_sum]
  exact Finset.sum_congr rfl fun p _=>by simp [b,← map_smul]
 obtain ⟨P,hP⟩:=(Filter.eventually_all.mpr trunc).exists
 let D:=(Matrix.detRowAlternating:(I -> ℤ) [⋀^I]→ₗ[ℤ] ℤ).toMultilinearMap
 have hid:(fun i=>∑ p ∈ P,b p i • w p)=(1:Matrix I I ℤ):=by
  ext i j
  simpa [w,Finset.sum_apply,Pi.single_apply,Matrix.one_apply,mul_comm,eq_comm] using congrFun (hP j) i
 have hn:D (fun i=>∑ p ∈ P,b p i • w p) ≠ 0:=by rw [hid]; change Matrix.det (1:Matrix I I ℤ) ≠ 0; simp
 rw [D.map_sum_finset] at hn
 obtain ⟨e,_,he⟩:=Finset.exists_ne_zero_of_sum_ne_zero hn
 rw [D.map_smul_univ] at he
 have hd:Matrix.det (fun i j=>v j (e i)) ≠ 0:=fun h=>he (by change _ • Matrix.det _=0; rw [h,smul_zero])
 exact ⟨⟨e,fun i j hij=>by_contra fun h=>hd (Matrix.det_zero_of_row_eq h (by simp [hij]))⟩,
  fun h=>hd ((Matrix.det_transpose _).trans h)⟩
end EilenbergGanea
namespace EilenbergGanea
section ChainProjection
variable {Γ D S T R:Type*} [Group Γ] [Group D]
theorem oL {v:S → Γ} {u:T → D} (φ:FreeGroup S →* FreeGroup T)
  (q:Γ → D) (L:aE Γ S →ₗ[ℤ] aE D T)
  (hv:∀ p w,q (p * aD v w)=q p * aD u (φ w))
  (he:∀ p s,L (Finsupp.single (p,s) 1)=aW u (φ (FreeGroup.of s)) (q p))
  (w:FreeGroup S) (g:Γ):L (aW v w g)=aW u (φ w) (q g):=
 pL φ q L.toAddMonoidHom.toMultiplicative hv he w g
theorem n0 (v:S -> Γ) (w:FreeGroup S) (g h:Γ) :
  aZ g (aW v w h)=aW v w (g*h):=by
 exact oL (.id _) (g * ·) (aZ g) (by simp [mul_assoc]) (by simp) w h
theorem Uz (v:S -> Γ) (q:Γ →* D) (w:FreeGroup S) (g:Γ) :
  dG q (aW v w g)=aW (fun s=>q (v s)) w (q g):=by
 exact oL (.id _) q (dG q) (by simp [o8]) (by simp) w g
def bC:aE Γ (S ⊕ T) →ₗ[ℤ] aE Γ T:=
 Finsupp.linearCombination ℤ fun p=>match p.2 with
  | .inl _=>0
  | .inr t=>Finsupp.single (p.1,t) 1
omit [Group Γ] in
@[simp] theorem cy6 (g:Γ) (s:S) (n:ℤ) :
  bC (Finsupp.single (g,Sum.inl s) n:aE Γ (S ⊕ T))=0:=by
 simp [bC]
omit [Group Γ] in
@[simp] theorem cv8 (g:Γ) (t:T) (n:ℤ) :
  bC (Finsupp.single (g,Sum.inr t) n:aE Γ (S ⊕ T)) =
   Finsupp.single (g,t) n:=by simp [bC]
theorem y7 (g:Γ) (c:aE Γ (S ⊕ T)) :
  bC (aZ g c)=aZ g (bC c):=by
 have he:(bC (Γ:=Γ) (S:=S) (T:=T)).comp (aZ g) =
   (aZ g).comp bC:=by
  apply Finsupp.lhom_ext
  rintro ⟨h,s | t⟩ n <;> simp
 exact LinearMap.congr_fun he c
theorem UC (q:Γ →* D) (c:aE Γ (S ⊕ T)) :
  bC (dG q c)=dG q (bC c):=by
 have he:(bC (Γ:=D) (S:=S) (T:=T)).comp (dG q) =
   (dG q).comp bC:=by
  apply Finsupp.lhom_ext
  rintro ⟨h,s | t⟩ n <;> simp
 exact LinearMap.congr_fun he c
def jY (v:S ⊕ T -> Γ) (r:R -> FreeGroup (S ⊕ T)) :
  aE Γ R →ₗ[ℤ] aE Γ T:=
 bC.comp (aO v r)
@[simp] theorem o2 (v:S ⊕ T -> Γ) (r:R -> FreeGroup (S ⊕ T))
  (g:Γ) (i:R) (n:ℤ) :
  jY v r (Finsupp.single (g,i) n) =
   n • bC (aW v (r i) g):=by
 simp [jY,aO]
theorem UF (v:S ⊕ T -> Γ) (r:R -> FreeGroup (S ⊕ T)) :
  b8 (jY v r):=by
 intro g c
 have he:(jY v r).comp (aZ g) =
   (aZ g).comp (jY v r):=by
  apply Finsupp.lhom_ext
  rintro ⟨h,i⟩ n
  simp only [LinearMap.comp_apply,j8,o2,map_smul]
  rw [<- y7,n0]
 exact LinearMap.congr_fun he c
theorem UG {I:Type*} [Fintype I] [DecidableEq I]
  (v:S ⊕ T -> Γ) (r:R -> FreeGroup (S ⊕ T))
  (A:aE Γ R ≃ₗ[ℤ] aE Γ T)
  (hA:A.toLinearMap=jY v r) (q:Γ →* D) (hq:Function.Surjective q) (j:I ↪ D × R) :
  ∃ e:I ↪ D × T,
   Matrix.det (fun i k=>bC
    (aW (fun s=>q (v s)) (r (j i).2) (j i).1) (e k)) ≠ 0:=by
 classical
 let L:=m6 q A.symm.toLinearMap
 apply oH _ (LinearMap.pi fun k=>(Finsupp.lapply (j k)).comp L)
 intro i
 have h (g:Γ) (t:R):L (bC (aW (fun s=>q (v s)) (r t) (q g))) =
   Finsupp.single (q g,t) 1:=by
  have hc:bC (aW v (r t) g)=A (Finsupp.single (g,t) 1):=by
   change _=A.toLinearMap _
   simp [hA]
  rw [← Uz,UC,hc,Uw q _ (b8.symm A (by rw [hA]; exact UF v r))]
  simp
 obtain ⟨g,hg⟩:=hq (j i).1
 have hi:=h g (j i).2
 rw [hg,Prod.mk.eta] at hi
 ext k
 change L _ (j k)=_
 simp [hi,Pi.single_apply,Finsupp.single_apply,j.injective.eq_iff,eq_comm]
end ChainProjection
open scoped Quaternion
section FiniteQuotientEquations
variable {Γ F S T R Z:Type*} [Group Γ] [Group F]
theorem yA [DecidableEq F] [DecidableEq S]
  (v:S -> F) (w:FreeGroup S) (g:F) (e:F × S) :
  dN (jP v w g) e=aW v w g e:=by
 have he:(FreeGroup.lift (fun i:F × S=>
   Multiplicative.ofAdd (if e=i then (1:ℤ) else 0))) =
   (Finsupp.applyAddHom e).toMultiplicative.comp
    (FreeGroup.lift (fun i:F × S=>Multiplicative.ofAdd (Finsupp.single i (1:ℤ)))):=by
  apply FreeGroup.ext_hom
  intro i
  simp [Finsupp.single_apply,eq_comm]
 simp only [dN,he,MonoidHom.comp_apply,Uh]
 rfl
omit [Group F] in
theorem vX (c:aE F (S ⊕ T)) (e:F × T) :
  bC c e=c (e.1,Sum.inr e.2):=by
 classical
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,Finsupp.add_apply,hc,hd]
 | single p n=>
   rcases p with ⟨g,s | t⟩
   ·simp
   ·simp [Finsupp.single_apply,Prod.ext_iff]
end FiniteQuotientEquations
end EilenbergGanea
namespace EilenbergGanea
open scoped Quaternion ContDiff
open Set
section FiniteQuotientSolvability
variable {F S T R Z:Type*} [Group F] [Fintype F] [Fintype Z]
theorem oR
  (v:S ⊕ T -> F) (r:Z ⊕ R -> FreeGroup (S ⊕ T)) (B:Finset R)
  (minor:∀ {n} (j:Fin n ↪ F × R),∃ e:Fin n ↪ F × T,
   Matrix.det (fun i k=>bC (aW v (r (.inr (j i).2)) (j i).1) (e k)) ≠ 0)
  (δ η:ℝ) (hδ:0 < δ) (hη1:η < 1)
  (barrier:∀ b:F -> S ⊕ T -> a3,
   (∀ g s,‖(b g (.inl s):ℍ)-1‖ <= η) ->
   (∀ i ∈ B,∀ g,aR v b (r (.inr i)) g=1) ->
   ‖oC v b r‖ ≠ δ)
  (a:F -> S -> a3) (ha:∀ g s,‖(a g s:ℍ)-1‖ < η/2) :
  ∃ b:F -> T -> a3,
   (∀ i ∈ B,∀ g,aR (H:=a3) v (dQ a b) (r (.inr i)) g=1) /\
   (∀ i g,‖(aR (H:=a3) v (dQ a b) (r (.inl i)) g:ℍ)-1‖ < δ):=by
 classical
 let I:=F × ↥B
 let J:=F × Z
 let eI:Fin (Fintype.card I) ≃ I:=(Fintype.equivFin I).symm
 let j:Fin (Fintype.card I) ↪ F × R:=
  eI.toEmbedding.trans ((Function.Embedding.refl F).prodMap (.subtype _))
 obtain ⟨e,hd⟩:=minor j
 let σ:=e.trans ((Function.Embedding.refl F).prodMap (Function.Embedding.inr (α:=S)))
 let w:Fin (Fintype.card I) -> FreeGroup (F × (S ⊕ T)):=
  fun k=>jP v (r (.inr (eI k).2.val)) (eI k).1
 let ρ:J -> FreeGroup (F × (S ⊕ T)):=
  fun k=>jP v (r (.inl k.2)) k.1
 have hdet:Matrix.det (fun i k=>dN (w i) (σ k)) ≠ 0:=by
  simp only [vX,MonoidHom.id_apply] at hd
  simp only [w,yA]
  exact hd
 let base:F × (S ⊕ T) -> a3:=fun p=>Sum.elim (a p.1) (fun _=>1) p.2
 have hbase (p):‖(base p:ℍ)-1‖ < 1:=by
  rcases p with ⟨g,s | t⟩
  ·exact (ha g s).trans (by linarith)
  ·simp [base]
 let arc:ℝ -> F × (S ⊕ T) -> a3:=fun t p=>jU (base p) t
 let L (t:ℝ) (x:Fin (Fintype.card I) -> a3):F -> S ⊕ T -> a3:=
  fun g s=>iG σ (arc t) x (g,s)
 have hleft (g:F) (s:S) (k:Fin (Fintype.card I)):σ k ≠ (g,.inl s):=by
  change ((e k).1,Sum.inr (e k).2) ≠ (g,Sum.inl s)
  simp
 have hsmall (t:ℝ) (x:Fin (Fintype.card I) -> a3) (g:F) (s:S) :
   ‖(L t x g (.inl s):ℍ)-1‖ <= η:=by
  dsimp only [L]
  rw [N8 σ _ x _ (hleft g s)]
  apply (qM (oK (a g s) t)).trans
  linarith [q8 (a g s) t,ha g s]
 have hword (b:F × (S ⊕ T) -> a3) (r:FreeGroup (S ⊕ T)) (g:F) :
   FreeGroup.lift b (jP v r g)=aR (H:=a3) v (fun g s=>b (g,s)) r g:=
  Ky v (fun g s=>b (g,s)) r g
 have rows (b:F × (S ⊕ T) -> a3) (hw:∀ k,FreeGroup.lift b (w k)=1) (i:R) (hi:i ∈ B) (g:F) :
   aR v (fun g s=>b (g,s)) (r (.inr i)) g=1:=by
  simpa only [w,Equiv.apply_symm_apply,hword] using hw (eI.symm (g,⟨i,hi⟩))
 obtain ⟨b,hfixed,hw,hρ⟩:=Tv σ w ρ arc
  (fun p=>Tk _ (hbase p)) (by intro p; simp [arc])
  hdet δ hδ (fun t _ x hx=>by
   simpa only [ρ,hword,oC,L] using
    barrier (L t x) (hsmall t x) (rows _ hx))
 let b':F -> T -> a3:=fun g t=>b (g,.inr t)
 have heval:(fun g s=>b (g,s))=dQ a b':=by
  funext g s
  rcases s with s | t
  ·rw [hfixed _ (hleft g s)]
   simp [arc,base,dQ]
  ·rfl
 refine ⟨b',?_,?_⟩
 ·simpa only [← heval] using rows b hw
 ·intro i g
  simpa only [ρ,Pi.sub_apply,Pi.one_apply,hword,heval] using
   (norm_le_pi_norm ((fun k=>(FreeGroup.lift b (ρ k):ℍ))-1) (g,i)).trans_lt hρ
end FiniteQuotientSolvability
end EilenbergGanea
namespace EilenbergGanea
open scoped Quaternion
section AlignedComparison
variable {Γ:Type u} {S T Z R:Type*} [Group Γ] [Group.ResiduallyFinite Γ] [Fintype Z]
theorem UK
  (v:S ⊕ T -> Γ) (r:Z ⊕ R -> FreeGroup (S ⊕ T)) (z:Z -> FreeGroup S)
  (hvT:∀ t,v (.inr t)=1)
  (hr:∀ i,aD v (r i)=1)
  (hz:∀ i,aD (fun s=>v (.inl s)) (z i)=1)
  (hp:(aD v).ker=Subgroup.normalClosure (Set.range r))
  (hinj:Function.Injective (aO v r))
  (hchain:∀ i,aW v (FreeGroup.map Sum.inl (z i)) 1=aW v (r (.inl i)) 1)
  (Q:aE Γ R ≃ₗ[ℤ] aE Γ T)
  (hQ:Q.toLinearMap=jY v (fun i=>r (.inr i))) :
  ∃ η:ℝ,0 < η /\ ∀ a:Γ -> S -> a3,
   (∀ g s,‖(a g s:ℍ)-1‖ < η) ->
   (∀ i g,aR (fun s=>v (.inl s)) a (z i) g=1) ->
   ∀ w:FreeGroup S,aD (fun s=>v (.inl s)) w=1 -> ∀ g,
    aR (fun s=>v (.inl s)) a w g=1:=by
 classical
 have hzn (i):FreeGroup.map Sum.inl (z i) ∈ Subgroup.normalClosure (Set.range r):=by
  rw [<- hp]
  change aD v (FreeGroup.map Sum.inl (z i))=1
  rw [KD,hz]
 have htn (t):FreeGroup.of (.inr t) ∈ Subgroup.normalClosure (Set.range r):=by
  rw [<- hp]
  change aD v (FreeGroup.of (.inr t))=1
  simpa [aD] using hvT t
 choose lz hlz using fun i=>Ob r (hzn i)
 choose lt hlt using fun t=>Ob r (htn t)
 have hc (i):((lz i).map (fun f=>gT v f 1)).sum =
   Finsupp.single (1,Sum.inl i) 1:=
  TQ v r hr hinj _ (.inl i) (hchain i) (lz i) (hlz i)
 obtain ⟨A,C,hC,hcomp⟩:=Ur v r hr z lz lt hlz hlt hc
 obtain ⟨δ,η,hδ,hδ1,hη,hη1,hc₁,hc₂⟩:=Ue C hC
 refine ⟨η/2,half_pos hη,?_⟩
 intro a ha haz
 let W:Γ × (Z ⊕ R) -> FreeGroup (S ⊕ T):=fun p=>r p.2
 let K:Γ × (Z ⊕ R) -> Set a3:=fun p=>match p.2 with
  | .inl _=>{b | ‖(b:ℍ)-1‖ <= δ}
  | .inr _=>{1}
 have hK (p):IsClosed (K p):=by
  rcases p with ⟨g,i | i⟩
  ·exact isClosed_le ((continuous_subtype_val.sub continuous_const).norm) continuous_const
  ·exact isClosed_singleton
 obtain ⟨b,hb⟩:=oA v a W Prod.fst K hK
  (fun b:a3=>‖(b:ℍ)-1‖ < η/2) (by simpa using half_pos hη) ha (by
   intro N J aF haF
   let:Fintype (Γ ⧸ N.toSubgroup):=Fintype.ofFinite _
   let q:=QuotientGroup.mk' N.toSubgroup
   let B:=A ∪ (J.image Prod.snd).toRight
   obtain ⟨bF,hord,hdis⟩:=oR (fun s=>q (v s)) r B
    (fun j=>UG v _ Q hQ q (QuotientGroup.mk'_surjective _) j) δ η hδ hη1 (by
     intro b hs ho he
     let f:=oC (fun s=>q (v s)) b r
     have h:‖f‖ ≤ C*(η+δ)*δ + C*η:=
      (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun p=>
       (hcomp q b η δ hη.le hδ.le hs (fun i hi=>ho i (Finset.mem_union_left _ hi))
        (fun i g=>(norm_le_pi_norm f (g,i)).trans he.le) p.2 p.1).trans
        (add_le_add le_rfl (min_le_right _ _))
     change ‖f‖ = δ at he
     rw [he] at h
     linarith [mul_lt_mul_of_pos_right hc₁ hδ]) aF haF
   refine ⟨bF,?_⟩
   rintro ⟨g,i | i⟩ hi d
   ·exact (hdis i d).le
   ·exact hord i (Finset.mem_union_right _ (Finset.mem_toRight.mpr
     (Finset.mem_image.mpr ⟨(g,.inr i),hi,rfl⟩))) d)
 have hord (i:R) (g:Γ):aR v (dQ a b) (r (.inr i)) g=1:=
  hb (g,.inr i)
 have hdis (i:Z) (g:Γ):‖(aR (H:=a3) v (dQ a b) (r (.inl i)) g:ℍ)-1‖ <= δ:=
  hb (g,.inl i)
 let f:Z × Γ -> ℝ:=fun p=>‖(aR (H:=a3) v (dQ a b) (r (.inl p.1)) p.2:ℍ)-1‖
 have half (M:ℝ) (hM:0 ≤ M) (hd:M ≤ δ) (hb:∀ p,f p ≤ M) (i:Z) (g:Γ):f (i,g) ≤ M/2:=by
  have h:=hcomp (MonoidHom.id Γ) (dQ a b) η M hη.le hM
   (fun g s=>(ha g s).le.trans (half_le_self hη.le)) (fun i _=>hord i) (fun i g=>hb (i,g)) i g
  have hz':aR v (dQ a b) (FreeGroup.map Sum.inl (z i)) g = 1:=by
   rw [r4]; exact haz i g
  change f (i,g) ≤ C*(η+M)*M + min ‖(aR (H:=a3) v (dQ a b) (FreeGroup.map Sum.inl (z i)) g:ℍ)-1‖ _ at h
  rw [hz'] at h
  simp [min_eq_left (mul_nonneg (by linarith:0 ≤ C) hη.le)] at h
  have hc:C*(η+M) ≤ C*(δ+η):=mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  linarith [mul_le_mul_of_nonneg_right (hc.trans hc₁.le) hM]
 have bound (n:ℕ):∀ p,f p ≤ δ*(1/2)^n:=by
  induction n with
  | zero=>simpa using fun p:Z × Γ=>hdis p.1 p.2
  | succ n ih=>
   intro p
   rw [pow_succ,← mul_assoc]
   simpa only [div_eq_mul_inv,one_mul] using half _ (by positivity) (mul_le_of_le_one_right hδ.le (pow_le_one₀ (by norm_num) (by norm_num))) ih p.1 p.2
 have hzero (p):f p=0:=by
  by_contra hn
  have hp:0 < f p:=lt_of_le_of_ne (norm_nonneg _) (Ne.symm hn)
  obtain ⟨n,hn⟩:=exists_pow_lt_of_lt_one (div_pos hp hδ) (by norm_num:(1/2:ℝ)<1)
  linarith [bound n p,(lt_div_iff₀ hδ).mp hn]
 have hdist (i:Z) (g:Γ):aR v (dQ a b) (r (.inl i)) g=1:=by
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp (hzero (i,g)))
 intro w hw g
 have hw':aD v (FreeGroup.map Sum.inl w)=1:=by
  rw [KD,hw]
 have h:=TA v (dQ a b) (Set.range r)
  (by rintro _ ⟨i,rfl⟩; exact hr i) hp
  (by rintro _ ⟨i | i,rfl⟩ g; exact hdist i g; exact hord i g)
  (FreeGroup.map Sum.inl w) hw' g
 simpa only [r4,dQ,Sum.elim_inl,Function.comp_def] using h
end AlignedComparison
end EilenbergGanea
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea
section WordRealization
variable {Γ S R:Type*} [Group Γ]
theorem ch1 (v:S -> Γ) (w:FreeGroup S)
    (hw:aD v w=1) (n:ℤ) (g:Γ) :
    aW v (w ^ n) g=n • aW v w g:=by
  induction n using Int.induction_on with
  | zero=>simp
  | succ n ih=>
      rw [zpow_add,zpow_one,d2,map_zpow,hw,one_zpow,mul_one,ih]
      simp [add_zsmul]
  | pred n ih=>
      rw [zpow_sub,zpow_one,d2,map_zpow,hw,one_zpow,mul_one,
        f9,hw,inv_one,mul_one,ih]
      simp only [sub_eq_add_neg,add_zsmul,neg_zsmul,one_zsmul]
theorem UN (v:S -> Γ) (hv:Function.Surjective (aD v))
    (r:R -> FreeGroup S) (hr:∀ i,aD v (r i)=1)
    (c:(Γ × R) →₀ ℤ) :
    ∃ w ∈ Subgroup.normalClosure (Set.range r),
      aW v w 1=aO v r c:=by
  classical
  induction c using Finsupp.induction with
  | zero=>exact ⟨1,Subgroup.one_mem _,by simp⟩
  | @single_add a n c ha hn ih=>
      obtain ⟨w,hw,hcw⟩:=ih
      obtain ⟨u,hu⟩:=hv a.1
      let z:=u * r a.2 * u⁻¹
      have hz:z ∈ Subgroup.normalClosure (Set.range r):=
        (Subgroup.normalClosure_normal (s:=Set.range r)).conj_mem _
          (Subgroup.subset_normalClosure (Set.mem_range_self a.2)) u
      have hzw:aD v z=1:=by simp [z,hr]
      refine ⟨z ^ n * w,Subgroup.mul_mem _ (Subgroup.zpow_mem _ hz n) hw,?_⟩
      rw [d2,map_zpow,hzw,one_zpow,mul_one,ch1 _ _ hzw,
        hcw,map_add]
      congr 1
      rw [n5 v u _ (hr a.2),one_mul,hu]
      simp [aO]
end WordRealization
section RelatorShears
variable {Γ S R I:Type*} [Group Γ]
theorem o7 (v:S -> Γ) (r:R -> FreeGroup S) :
    b8 (aO v r):=by
  intro g c
  have he:(aO v r).comp (aZ g) =
      (aZ g).comp (aO v r):=by
    apply Finsupp.lhom_ext
    rintro ⟨h,i⟩ n
    simp only [LinearMap.comp_apply,j8,aO,
      Finsupp.linearCombination_single,map_smul,n0]
  exact LinearMap.congr_fun he c
theorem Oc (v:S -> Γ) (r:R -> FreeGroup S)
  (hr:∀ i,aD v (r i)=1) :
  Subgroup.normalClosure (Set.range r) <= (aD v).ker:=by
 apply Subgroup.normalClosure_le_normal
 rintro _ ⟨i,rfl⟩
 exact hr i
@[simp] theorem f1 (v:S -> Γ) (r:R -> FreeGroup S)
  (g:Γ) (i:R) (n:ℤ) :
  aO v r (Finsupp.single (g,i) n)=n • aW v (r i) g:=by
 simp [aO]
theorem Lz (v:S -> Γ) (hv:Function.Surjective (aD v))
    (r:R -> FreeGroup S) (u:I -> FreeGroup S)
    (hr:∀ i,aD v (r i)=1) (hu:∀ i,aD v (u i)=1)
    (C:aE Γ I →ₗ[ℤ] aE Γ R) (hC:b8 C) :
    ∃ u':I -> FreeGroup S,
      (∀ i,aD v (u' i)=1) /\
      Subgroup.normalClosure (Set.range r ∪ Set.range u') =
        Subgroup.normalClosure (Set.range r ∪ Set.range u) /\
      aO v u'=aO v u + (aO v r).comp C:=by
  classical
  choose p hp hc using fun i=>UN v hv r hr (C (Finsupp.single (1,i) 1))
  let u':I -> FreeGroup S:=fun i=>u i * p i
  have hpr (i):aD v (p i)=1:=Oc v r hr (hp i)
  have hu' (i):aD v (u' i)=1:=by simp [u',hu,hpr]
  refine ⟨u',hu',?_,?_⟩
  · apply le_antisymm
    · apply Subgroup.normalClosure_le_normal
      rintro _ (⟨i,rfl⟩ | ⟨i,rfl⟩)
      · exact Subgroup.subset_normalClosure (Or.inl (Set.mem_range_self i))
      · exact Subgroup.mul_mem _ (Subgroup.subset_normalClosure (Or.inr (Set.mem_range_self i)))
          (Subgroup.normalClosure_mono Set.subset_union_left (hp i))
    · apply Subgroup.normalClosure_le_normal
      rintro _ (⟨i,rfl⟩ | ⟨i,rfl⟩)
      · exact Subgroup.subset_normalClosure (Or.inl (Set.mem_range_self i))
      · have h:u' i * (p i)⁻¹ ∈ Subgroup.normalClosure (Set.range r ∪ Set.range u'):=
          Subgroup.mul_mem _ (Subgroup.subset_normalClosure (Or.inr (Set.mem_range_self i)))
            (Subgroup.inv_mem _ (Subgroup.normalClosure_mono Set.subset_union_left (hp i)))
        simpa [u'] using h
  · have hb (i):aW v (u' i) 1=aW v (u i) 1 +
        aO v r (C (Finsupp.single (1,i) 1)):=by
      simp only [u',d2,hu,mul_one,hc]
    have hbg (g:Γ) (i:I):aW v (u' i) g=aW v (u i) g +
        aO v r (C (Finsupp.single (g,i) 1)):=by
      have h:=congrArg (aZ g) (hb i)
      rw [map_add,n0,n0,mul_one,
        <- o7 v r g,<- hC g,j8,mul_one] at h
      exact h
    apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    have hn:Finsupp.single (g,i) n=n • Finsupp.single (g,i) (1:ℤ):=by simp
    simpa only [hn,map_smul,LinearMap.add_apply,LinearMap.comp_apply,
      f1,one_smul,smul_add] using congrArg (n • ·) (hbg g i)
theorem UO (v:S -> Γ) (hv:Function.Surjective (aD v))
    (r:R -> FreeGroup S) (u:I -> FreeGroup S)
    (hr:∀ i,aD v (r i)=1) (hu:∀ i,aD v (u i)=1)
    (A:aE Γ R ≃ₗ[ℤ] aE Γ I)
    (hA:b8 A.toLinearMap) :
    ∃ (r':R -> FreeGroup S) (u':I -> FreeGroup S),
      (∀ i,aD v (r' i)=1) /\ (∀ i,aD v (u' i)=1) /\
      Subgroup.normalClosure (Set.range r' ∪ Set.range u') =
        Subgroup.normalClosure (Set.range r ∪ Set.range u) /\
      aO v r'=-((aO v u).comp A.toLinearMap) /\
      aO v u'=(aO v r).comp A.symm.toLinearMap:=by
  have hAi:=b8.symm A hA
  have hnA:b8 (-A.toLinearMap):=by
    intro g c
    simp only [LinearMap.neg_apply,map_neg]
    exact congrArg Neg.neg (hA g c)
  obtain ⟨u₁,hu₁,hN₁,hD₁⟩:=Lz v hv r u hr hu A.symm.toLinearMap hAi
  obtain ⟨r₂,hr₂,hN₂,hD₂⟩:=Lz v hv u₁ r hu₁ hr (-A.toLinearMap) hnA
  have hD₂':aO v r₂=-((aO v u).comp A.toLinearMap):=by
    rw [hD₂,hD₁]
    ext c
    simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.neg_apply,
      map_neg,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
    abel_nf
  obtain ⟨u₃,hu₃,hN₃,hD₃⟩:=Lz v hv r₂ u₁ hr₂ hu₁ A.symm.toLinearMap hAi
  refine ⟨r₂,u₃,hr₂,hu₃,?_,hD₂',?_⟩
  · rw [hN₃,Set.union_comm (Set.range r₂) (Set.range u₁),hN₂,
      Set.union_comm (Set.range u₁) (Set.range r),hN₁]
  · rw [hD₃,hD₁,hD₂']
    ext c
    simp only [LinearMap.add_apply,LinearMap.comp_apply,LinearMap.neg_apply,
      LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
    abel_nf
end RelatorShears
section CycleSpaces
variable {Γ S T U R:Type*} [Group Γ]
def bY (v:S -> Γ):aE Γ S →ₗ[ℤ] (Γ →₀ ℤ):=
 Finsupp.linearCombination ℤ (fun p:Γ × S=>
  Finsupp.single (p.1 * v p.2) 1 - Finsupp.single p.1 1)
@[simp] theorem Od (v:S -> Γ) (g:Γ) (s:S) (n:ℤ) :
  bY v (Finsupp.single (g,s) n) =
   n • (Finsupp.single (g * v s) 1 - Finsupp.single g 1):=by
 simp [bY]
theorem mJ (v:S -> Γ) (w:FreeGroup S) (g:Γ) :
  bY v (aW v w g) =
   Finsupp.single (g * aD v w) 1 - Finsupp.single g 1:=by
 induction w using FreeGroup.induction_on generalizing g with
 | C1=>simp
 | of s=>simp [aD]
 | inv_of s _ih=>simp [f9,aD]
 | mul w z hw hz=>
   rw [d2,map_add,hw,hz,map_mul]
   simp only [mul_assoc]
   abel
abbrev cycles (v:S -> Γ):=LinearMap.ker (bY v)
theorem UZ (v:S -> Γ) (r:R -> FreeGroup S)
  (hr:∀ i,aD v (r i)=1) :
  (bY v).comp (aO v r)=0:=by
 apply Finsupp.lhom_ext
 rintro ⟨g,i⟩ n
 simp [mJ,hr]
def zU (v:S -> Γ) (r:R -> FreeGroup S)
  (hr:∀ i,aD v (r i)=1):aE Γ R →ₗ[ℤ] cycles v:=
 (aO v r).codRestrict _ (fun c=>by
  rw [LinearMap.mem_ker]
  exact LinearMap.congr_fun (UZ v r hr) c)
@[simp] theorem dr0 (v:S -> Γ) (r:R -> FreeGroup S)
  (hr:∀ i,aD v (r i)=1) (c:aE Γ R) :
  (zU v r hr c:aE Γ S)=aO v r c:=rfl
@[simp] theorem do2 (v:S -> Γ) :
  aO v FreeGroup.of=LinearMap.id:=by
 apply Finsupp.lhom_ext
 rintro ⟨g,s⟩ n
 simp
end CycleSpaces
section SumChains
variable {Γ S T:Type*}
def aV:aE Γ (S ⊕ T) ≃ₗ[ℤ] aE Γ S × aE Γ T:=
 (Finsupp.domLCongr (Equiv.prodSumDistrib Γ S T)).trans (Finsupp.sumFinsuppLEquivProdFinsupp ℤ)
@[simp] theorem dp0 (c:aE Γ (S ⊕ T)) (g:Γ) (s:S) :
  (aV c).1 (g,s)=c (g,Sum.inl s):=by
 rfl
@[simp] theorem do3 (c:aE Γ (S ⊕ T)) (g:Γ) (t:T) :
  (aV c).2 (g,t)=c (g,Sum.inr t):=by
 rfl
@[simp] theorem ad2 (g:Γ) (s:S) (n:ℤ) :
  aV (Finsupp.single (g,Sum.inl s) n:aE Γ (S ⊕ T)) =
   (Finsupp.single (g,s) n,0):=by
 classical
 apply Prod.ext
 ·ext ⟨h,i⟩
  simp [Finsupp.single_apply]
 ·ext ⟨h,i⟩
  simp
@[simp] theorem z9 (g:Γ) (t:T) (n:ℤ) :
  aV (Finsupp.single (g,Sum.inr t) n:aE Γ (S ⊕ T)) =
   (0,Finsupp.single (g,t) n):=by
 classical
 apply Prod.ext
 ·ext ⟨h,i⟩
  simp
 ·ext ⟨h,i⟩
  simp [Finsupp.single_apply]
end SumChains
section TrivialGenerators
variable {Γ S T:Type*} [Group Γ]
theorem Oe (v:S -> Γ) (c:aE Γ (S ⊕ T)) :
  bY (Sum.elim v (fun _:T=>1)) c =
   bY v (aV c).1:=by
 have h:bY (Sum.elim v (fun _:T=>1)) =
   (bY v).comp ((LinearMap.fst ℤ _ _).comp aV.toLinearMap):=by
  apply Finsupp.lhom_ext
  rintro ⟨g,s | t⟩ n <;> simp
 exact LinearMap.congr_fun h c
def D7 (v:S -> Γ) :
  cycles (Sum.elim v (fun _:T=>1)) ≃ₗ[ℤ] cycles v × aE Γ T where
 toFun c:=(⟨(aV c.val).1,by
  rw [LinearMap.mem_ker,<- Oe]
  exact c.property⟩,(aV c.val).2)
 invFun c:=⟨aV.symm (c.1.val,c.2),by
  rw [LinearMap.mem_ker,Oe,LinearEquiv.apply_symm_apply]
  exact c.1.property⟩
 left_inv c:=by
  apply Subtype.ext
  exact aV.symm_apply_apply c.val
 right_inv c:=by
  apply Prod.ext
  ·apply Subtype.ext
   exact congrArg Prod.fst (aV.apply_symm_apply (c.1.val,c.2))
  ·exact congrArg (fun p:aE Γ S × aE Γ T=>p.2) (aV.apply_symm_apply (c.1.val,c.2))
 map_add' c d:=by
  apply Prod.ext
  ·apply Subtype.ext
   exact congrArg Prod.fst (aV.map_add c.val d.val)
  ·exact congrArg (fun p:aE Γ S × aE Γ T=>p.2) (aV.map_add c.val d.val)
 map_smul' n c:=by
  apply Prod.ext
  ·apply Subtype.ext
   exact congrArg Prod.fst (aV.map_smul n c.val)
  ·exact congrArg (fun p:aE Γ S × aE Γ T=>p.2) (aV.map_smul n c.val)
end TrivialGenerators
section WordEquivalence
variable {Γ S T:Type*} [Group Γ]
theorem Oi (v:S -> Γ) (w:T -> Γ) (e:FreeGroup S →* FreeGroup T)
  (he:(aD w).comp e=aD v) (a:FreeGroup S) (g:Γ) :
  aO w (fun s=>e (FreeGroup.of s)) (aW v a g) =
   aW w (e a) g:=by
 refine oL e id _ ?_ ?_ a g
 ·intro p z
  rw [← DFunLike.congr_fun he z]; rfl
 ·simp
theorem U3 (v:S -> Γ) (w:T -> Γ) (e:FreeGroup S →* FreeGroup T)
  (he:(aD w).comp e=aD v) :
  (bY w).comp (aO w (fun s=>e (FreeGroup.of s)))=bY v:=by
 apply Finsupp.lhom_ext
 rintro ⟨g,s⟩ n
 have hs:aD w (e (FreeGroup.of s))=v s:=by
  simpa [aD] using DFunLike.congr_fun he (FreeGroup.of s)
 simp [mJ,hs]
private theorem AO (v:S → Γ) (w:T → Γ) (e:FreeGroup S ≃* FreeGroup T)
  (he:(aD w).comp e.toMonoidHom=aD v) :
  (aO w (fun s=>e (FreeGroup.of s))).comp
   (aO v (fun t=>e.symm (FreeGroup.of t)))=LinearMap.id:=by
 apply Finsupp.lhom_ext
 rintro ⟨g,t⟩ n
 simpa using congrArg (n • ·) (Oi v w e.toMonoidHom he (e.symm (FreeGroup.of t)) g)
def lJ (v:S -> Γ) (w:T -> Γ) (e:FreeGroup S ≃* FreeGroup T)
  (he:(aD w).comp e.toMonoidHom=aD v) :
  aE Γ S ≃ₗ[ℤ] aE Γ T where
 __:=aO w (fun s=>e (FreeGroup.of s))
 invFun:=aO v (fun t=>e.symm (FreeGroup.of t))
 left_inv:=LinearMap.congr_fun (AO w v e.symm (by
  ext t
  simpa using (DFunLike.congr_fun he (e.symm (FreeGroup.of t))).symm))
 right_inv:=LinearMap.congr_fun (AO v w e he)
def Dr (v:S -> Γ) (w:T -> Γ) (e:FreeGroup S ≃* FreeGroup T)
  (he:(aD w).comp e.toMonoidHom=aD v):cycles v ≃ₗ[ℤ] cycles w:=
 (lJ v w e he).ofSubmodules (cycles v) (cycles w) (by
  ext c
  rw [Submodule.mem_map_equiv]
  change bY v ((lJ v w e he).symm c)=0 ↔ bY w c=0
  have h:=LinearMap.congr_fun (U3 v w e.toMonoidHom he)
   ((lJ v w e he).symm c)
  change bY w (lJ v w e he ((lJ v w e he).symm c)) =
   bY v ((lJ v w e he).symm c) at h
  rw [LinearEquiv.apply_symm_apply] at h
  rw [<- h])
end WordEquivalence
section TrivialPresentationExtension
variable {Γ S T R:Type*} [Group Γ]
def nP:FreeGroup (S ⊕ T) →* FreeGroup S:=
 FreeGroup.lift (Sum.elim FreeGroup.of (fun _=>1))
def dH (r:R -> FreeGroup S):R ⊕ T -> FreeGroup (S ⊕ T):=
 Sum.elim (fun i=>FreeGroup.map Sum.inl (r i)) (fun t=>FreeGroup.of (.inr t))
theorem zE (v:S → Γ) (w:T → Γ) (a:FreeGroup S) :
  aD (Sum.elim v w) (FreeGroup.map Sum.inl a)=aD v a:=by
 exact KD _ _ _
theorem B9 (v:S → Γ) (hv:Function.Surjective (aD v)) :
  Function.Surjective (aD (Sum.elim v (fun _:T=>1))):=by
 intro y
 obtain ⟨a,rfl⟩:=hv y
 exact ⟨_,zE v _ a⟩
theorem rV {v:S → Γ} {r:R → FreeGroup S}
  (hp:(aD v).ker = Subgroup.normalClosure (Set.range r)) (i:R):aD v (r i)=1:=by
 change r i ∈ (aD v).ker
 rw [hp]
 exact Subgroup.subset_normalClosure (Set.mem_range_self i)
theorem g9 (v:S -> Γ) (r:R -> FreeGroup S)
  (hr:∀ i,aD v (r i)=1) (i:R ⊕ T) :
  aD (Sum.elim v (fun _:T=>1)) (dH r i)=1:=by
 rcases i with i | t
 ·change aD _ (FreeGroup.map Sum.inl (r i))=1
  exact (zE v _ _).trans (hr i)
 ·simp [dH,aD]
theorem Oj (v:S -> Γ) (r:R -> FreeGroup S)
  (hp:(aD v).ker=Subgroup.normalClosure (Set.range r)) :
  (aD (Sum.elim v (fun _:T=>1))).ker =
   Subgroup.normalClosure (Set.range (dH r:R ⊕ T -> _)):=by
 let N:=Subgroup.normalClosure (Set.range (dH r:R ⊕ T -> _))
 apply le_antisymm
 ·intro w hw
  have hcomp:(aD v).comp nP =
    aD (Sum.elim v (fun _:T=>1)):=by
   apply FreeGroup.ext_hom
   intro s
   rcases s with s | t <;> simp [nP,aD]
  have hker:nP w ∈ Subgroup.normalClosure (Set.range r):=by
   rw [<- hp]
   exact (DFunLike.congr_fun hcomp w).trans hw
  have hmap:FreeGroup.map Sum.inl (nP w) ∈ N:=by
   apply Subgroup.normalClosure_mono (s:=(FreeGroup.map Sum.inl) '' Set.range r)
    (by rintro _ ⟨a,⟨i,rfl⟩,rfl⟩; exact ⟨Sum.inl i,rfl⟩)
   exact Subgroup.comap_normalClosure_image_ge _ (FreeGroup.map Sum.inl) hker
  have heq:(QuotientGroup.mk' N:FreeGroup (S ⊕ T) →* _) =
    ((QuotientGroup.mk' N).comp (FreeGroup.map Sum.inl)).comp nP:=by
   apply FreeGroup.ext_hom
   intro s
   rcases s with s | t
   ·simp [nP]
   ·simp only [MonoidHom.comp_apply,nP,FreeGroup.lift_apply_of,Sum.elim_inr,map_one]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.subset_normalClosure ⟨Sum.inr t,rfl⟩
  apply (QuotientGroup.eq_one_iff _).mp
  change (QuotientGroup.mk' N) w=1
  rw [DFunLike.congr_fun heq w]
  exact (QuotientGroup.eq_one_iff _).mpr hmap
 ·exact Oc _ _ (g9 v r (rV hp))
theorem LD (v:S -> Γ) (w:FreeGroup S) (g:Γ) :
  aV (aW (Sum.elim v (fun _:T=>1)) (FreeGroup.map Sum.inl w) g) =
   (aW v w g,0):=by
 induction w using FreeGroup.induction_on generalizing g with
 | C1=>simp only [map_one,N9,map_zero]; rfl
 | of s=>simp
 | inv_of s _ih=>simp [f9,aD]
 | mul w z hw hz=>
  simp only [map_mul,d2,map_add,hw,hz,zE,Prod.mk_add_mk,add_zero]
theorem U4 (v:S -> Γ) (r:R -> FreeGroup S)
  (c:aE Γ (R ⊕ T)) :
  aV (aO (Sum.elim v (fun _:T=>1))
   (dH r) c) =
   (aO v r (aV c).1,(aV c).2):=by
 have he:aV.toLinearMap.comp (aO
   (Sum.elim v (fun _:T=>1)) (dH r)) =
   (((aO v r).comp (LinearMap.fst ℤ _ _)).prod
    (LinearMap.snd ℤ _ _)).comp aV.toLinearMap:=by
  apply Finsupp.lhom_ext
  rintro ⟨g,i | t⟩ n
  ·simp [dH,LD]
  ·simp [dH]
 exact LinearMap.congr_fun he c
end TrivialPresentationExtension
section UnitExtensionBasis
variable {Γ S T R:Type*} [Group Γ]
def u5 (v:S -> Γ) (B:aE Γ R ≃ₗ[ℤ] cycles v) :
  aE Γ (R ⊕ T) ≃ₗ[ℤ] cycles (Sum.elim v (fun _:T=>1)):=
 aV.trans ((B.prodCongr (LinearEquiv.refl ℤ (aE Γ T))).trans
  (D7 v).symm)
theorem Ol (v:S -> Γ) (r:R -> FreeGroup S)
  (B:aE Γ R ≃ₗ[ℤ] cycles v)
  (hB:∀ c,(B c:aE Γ S)=aO v r c)
  (c:aE Γ (R ⊕ T)) :
  (u5 v B c:aE Γ (S ⊕ T)) =
   aO (Sum.elim v (fun _:T=>1)) (dH r) c:=by
 apply aV.injective
 rw [U4]
 change aV (aV.symm
  ((B (aV c).1).val,(aV c).2))=_
 rw [LinearEquiv.apply_symm_apply,hB]
theorem U5 (v:S -> Γ)
  (r:R -> FreeGroup S) (u:T -> FreeGroup S)
  (E:aE Γ R ≃ₗ[ℤ] cycles v)
  (B:aE Γ T ≃ₗ[ℤ] cycles v)
  (hE:∀ c,(E c:aE Γ S)=aO v r c)
  (hB:∀ c,(B c:aE Γ S)=aO v u c) :
  b8 (E.trans B.symm).toLinearMap:=by
 intro g c
 apply B.injective
 apply Subtype.ext
 change (B (B.symm (E (aZ g c)))).val =
  (B (aZ g (B.symm (E c)))).val
 rw [B.apply_symm_apply,hE,hB,o7 v u g]
 rw [<- hB,B.apply_symm_apply,hE]
 exact o7 v r g c
end UnitExtensionBasis
section Nielsen
variable {Γ S T A R:Type*} [Group Γ]
def gW (a:T -> FreeGroup S):FreeGroup (S ⊕ T) →* FreeGroup (S ⊕ T):=
 FreeGroup.lift (Sum.elim (fun s=>FreeGroup.of (.inl s))
  (fun t=>FreeGroup.of (.inr t) * FreeGroup.map Sum.inl (a t)))
@[simp] theorem dq4 (a:T -> FreeGroup S) (s:S) :
  gW a (FreeGroup.of (.inl s))=FreeGroup.of (.inl s):=by
 simp [gW]
@[simp] theorem ch0 (a:T -> FreeGroup S) (t:T) :
  gW a (FreeGroup.of (.inr t)) =
   FreeGroup.of (.inr t) * FreeGroup.map Sum.inl (a t):=by
 simp [gW]
@[simp] theorem dt0 (a:T -> FreeGroup S) (w:FreeGroup S) :
  gW a (FreeGroup.map Sum.inl w)=FreeGroup.map Sum.inl w:=by
 have h:(gW a).comp (FreeGroup.map Sum.inl)=FreeGroup.map Sum.inl:=by
  apply FreeGroup.ext_hom
  intro s
  simp [gW]
 exact DFunLike.congr_fun h w
def nC (a:T -> FreeGroup S):FreeGroup (S ⊕ T) ≃* FreeGroup (S ⊕ T) where
 __:=gW a
 invFun:=gW (fun t=>(a t)⁻¹)
 left_inv w:=by
  have h:(gW (fun t=>(a t)⁻¹)).comp (gW a)=MonoidHom.id _:=by
   apply FreeGroup.ext_hom
   intro s
   rcases s with s | t <;> simp [mul_assoc]
  exact DFunLike.congr_fun h w
 right_inv w:=by
  have h:(gW a).comp (gW (fun t=>(a t)⁻¹))=MonoidHom.id _:=by
   apply FreeGroup.ext_hom
   intro s
   rcases s with s | t <;> simp [mul_assoc]
  exact DFunLike.congr_fun h w
@[simp] theorem do1 (a:T -> FreeGroup S) (w:FreeGroup (S ⊕ T)) :
  nC a w=gW a w:=rfl
theorem Om (v:S -> Γ) (w:T -> Γ) (a:T -> FreeGroup S) :
  (aD (Sum.elim v w)).comp (nC a).toMonoidHom =
   aD (Sum.elim v (fun t=>w t * aD v (a t))):=by
 apply FreeGroup.ext_hom
 intro s
 rcases s with s | t
 ·simp [gW,aD]
 ·change aD (Sum.elim v w) (gW a (FreeGroup.of (.inr t)))=_
  rw [ch0,map_mul,zE]
  simp [aD]
theorem k2 (v:S -> Γ) (w:T -> Γ)
  (e:FreeGroup S ≃* FreeGroup T)
  (he:(aD w).comp e.toMonoidHom=aD v)
  (r:R -> FreeGroup S)
  (hp:(aD v).ker=Subgroup.normalClosure (Set.range r)) :
  (aD w).ker=Subgroup.normalClosure (Set.range (fun i=>e (r i))):=by
 have hi:(aD v).comp e.symm.toMonoidHom=aD w:=by
  apply FreeGroup.ext_hom
  intro t
  simpa using (DFunLike.congr_fun he (e.symm (FreeGroup.of t))).symm
 change (aD w).ker=Subgroup.normalClosure (Set.range (e ∘ r))
 rw [Set.range_comp]
 change (aD w).ker=Subgroup.normalClosure (e.toMonoidHom '' Set.range r)
 rw [<- Subgroup.map_normalClosure _ e.toMonoidHom e.surjective,<- hp]
 ext a
 constructor
 ·intro ha
  refine ⟨e.symm a,?_,e.apply_symm_apply a⟩
  exact (DFunLike.congr_fun hi a).trans ha
 ·rintro ⟨b,hb,rfl⟩
  exact (DFunLike.congr_fun he b).trans hb
theorem uZ (v:S → Γ) (w:T → Γ) (e:FreeGroup S ≃* FreeGroup T)
  (he:(aD w).comp e.toMonoidHom=aD v) (r:R → FreeGroup S) :
  (aO w (fun s=>e (FreeGroup.of s))).comp (aO v r) =
   aO w (fun i=>e (r i)):=by
 apply Finsupp.lhom_ext
 rintro ⟨g,i⟩ n
 simp only [LinearMap.comp_apply,f1,map_zsmul]
 exact congrArg (n • ·) (Oi v w e.toMonoidHom he (r i) g)
end Nielsen
section GeneratorAlignment
variable {Γ S T A R:Type*} [Group Γ]
def freeGroupCongr (e:S ≃ T):FreeGroup S ≃* FreeGroup T where
 __:=FreeGroup.map e
 invFun:=FreeGroup.map e.symm
 left_inv w:=by simpa [Function.comp_def] using FreeGroup.map.comp e e.symm w
 right_inv w:=by simpa [Function.comp_def] using FreeGroup.map.comp e.symm e w
@[simp] theorem Iz (e:S ≃ T) (w:FreeGroup S) :
  freeGroupCongr e w=FreeGroup.map e w:=rfl
theorem l8 (v:S -> Γ) (w:T -> Γ) (e:S ≃ T)
  (h:∀ s,w (e s)=v s) :
  (aD w).comp (freeGroupCongr e).toMonoidHom=aD v:=by
 apply FreeGroup.ext_hom
 intro s
 simpa [aD] using h s
structure BasedPresentation (v:S → Γ) (R:Type*) where
 rel:R → FreeGroup S
 normal:(aD v).ker = Subgroup.normalClosure (Set.range rel)
 basis:aE Γ R ≃ₗ[ℤ] cycles v
 realizes:∀ c,(basis c).val = aO v rel c

def BasedPresentation.extend {v:S → Γ} (P:BasedPresentation v R) :
  BasedPresentation (Sum.elim v (fun _:T=>1)) (R ⊕ T):=
 ⟨dH P.rel,Oj v _ P.normal,u5 v P.basis,Ol v _ _ P.realizes⟩

def BasedPresentation.transport {v:S → Γ} {w:T → Γ} (P:BasedPresentation v R)
  (e:FreeGroup S ≃* FreeGroup T) (h:(aD w).comp e.toMonoidHom = aD v) :
  BasedPresentation w R:=
 ⟨fun i=>e (P.rel i),k2 v w e h _ P.normal,P.basis.trans (Dr v w e h),by
  intro c
  change aO w (fun s=>e (FreeGroup.of s)) (P.basis c).val = _
  rw [P.realizes]
  exact LinearMap.congr_fun (uZ v w e h P.rel) c⟩
def U6 (v:S → Γ) (hv:Function.Surjective (aD v))
  (a:A → Γ) (ha:Function.Surjective (aD a)) (P:BasedPresentation a R) :
  BasedPresentation (Sum.elim v (fun _:A=>1)) (R ⊕ S):=by
 classical
 choose f hf using fun s=>ha (v s)
 choose g hg using fun t=>hv (a t)
 let v₀:A ⊕ S -> Γ:=Sum.elim a (fun _=>1)
 let v₁:A ⊕ S -> Γ:=Sum.elim a v
 let v₂:S ⊕ A -> Γ:=Sum.elim v a
 let v₃:S ⊕ A -> Γ:=Sum.elim v (fun _=>1)
 let e₁:=nC (fun s=>(f s)⁻¹)
 let e₂:=freeGroupCongr (Equiv.sumComm A S)
 let e₃:=nC g
 have he₁:(aD v₁).comp e₁.toMonoidHom=aD v₀:=by
  change (aD (Sum.elim a v)).comp
   (nC (fun s=>(f s)⁻¹)).toMonoidHom=_
  simpa only [map_inv,hf,mul_inv_cancel] using
   Om a v (fun s=>(f s)⁻¹)
 have he₂:(aD v₂).comp e₂.toMonoidHom=aD v₁:=by
  apply l8
  intro s
  rcases s with t | s <;> rfl
 have he₃:(aD v₃).comp e₃.toMonoidHom=aD v₂:=by
  change (aD (Sum.elim v (fun _:A=>1))).comp
   (nC g).toMonoidHom=_
  simpa only [one_mul,hg] using Om v (fun _:A=>1) g
 let e:=(e₁.trans e₂).trans e₃
 apply P.extend.transport e
 ext x
 exact (DFunLike.congr_fun he₃ _).trans ((DFunLike.congr_fun he₂ _).trans (DFunLike.congr_fun he₁ _))
end GeneratorAlignment
section RelatorBlocks
variable {Γ S T R I:Type*} [Group Γ]
theorem U7 (v:S -> Γ) (r:R -> FreeGroup S) (c:aE Γ R) :
  aV (aO (Sum.elim v (fun _:T=>1))
   (fun i=>FreeGroup.map Sum.inl (r i)) c)=(aO v r c,0):=by
 have h:aV.toLinearMap.comp (aO
   (Sum.elim v (fun _:T=>1)) (fun i=>FreeGroup.map Sum.inl (r i))) =
   (aO v r).prod 0:=by
  apply Finsupp.lhom_ext
  rintro ⟨g,i⟩ n
  simp [LD]
 exact LinearMap.congr_fun h c
theorem U8 (v:S -> Γ) (c:aE Γ T) :
  aV (aO (Sum.elim v (fun _:T=>1))
   (fun i=>FreeGroup.of (.inr i)) c)=(0,c):=by
 have h:aV.toLinearMap.comp (aO
   (Sum.elim v (fun _:T=>1)) (fun i=>FreeGroup.of (.inr i))) =
   (0:aE Γ T →ₗ[ℤ] aE Γ S).prod LinearMap.id:=by
  apply Finsupp.lhom_ext
  rintro ⟨g,i⟩ n
  simp
 exact LinearMap.congr_fun h c
theorem Oo {α β γ:Type*} (f:α -> γ) (g:β -> γ) :
  Set.range (Sum.elim f g)=Set.range f ∪ Set.range g:=by
 ext x
 constructor
 ·rintro ⟨a | b,rfl⟩
  ·exact Or.inl ⟨a,rfl⟩
  ·exact Or.inr ⟨b,rfl⟩
 ·rintro (⟨a,rfl⟩ | ⟨b,rfl⟩)
  ·exact ⟨Sum.inl a,rfl⟩
  ·exact ⟨Sum.inr b,rfl⟩
theorem zF (v:S -> Γ) (hv:Function.Surjective (aD v))
  (r:R -> FreeGroup S) (z:I -> FreeGroup S)
  (hp:(aD v).ker=Subgroup.normalClosure (Set.range r))
  (E:aE Γ R ≃ₗ[ℤ] cycles v) (B:aE Γ I ≃ₗ[ℤ] cycles v)
  (hE:∀ c,(E c:aE Γ S)=aO v r c)
  (hB:∀ c,(B c:aE Γ S)=aO v z c) :
  ∃ (r':R -> FreeGroup (S ⊕ I)) (u':I -> FreeGroup (S ⊕ I)),
   (aD (Sum.elim v (fun _:I=>1))).ker =
    Subgroup.normalClosure (Set.range (Sum.elim r' u')) /\
   (∀ c,aV (aO (Sum.elim v (fun _:I=>1)) r' c) =
    (0,-(E.trans B.symm) c)) /\
   ∀ c,aV (aO (Sum.elim v (fun _:I=>1)) u' c) =
    ((B c).val,0):=by
 let w:S ⊕ I -> Γ:=Sum.elim v (fun _=>1)
 let r₀:R -> FreeGroup (S ⊕ I):=fun i=>FreeGroup.map Sum.inl (r i)
 let u₀:I -> FreeGroup (S ⊕ I):=fun i=>FreeGroup.of (.inr i)
 let A:aE Γ R ≃ₗ[ℤ] aE Γ I:=E.trans B.symm
 have hA:b8 A.toLinearMap:=U5 v r z E B hE hB
 have hw:=B9 (T:=I) v hv
 have hr₀:∀ i,aD w (r₀ i)=1:=fun i=>
  g9 v r (rV hp) (.inl i)
 have hu₀:∀ i,aD w (u₀ i)=1:=fun i=>
  g9 v r (rV hp) (.inr i)
 obtain ⟨r',u',hr',hu',hN,hDr,hDu⟩:=UO w hw r₀ u₀ hr₀ hu₀ A hA
 have hcr (c):aV (aO w r' c)=(0,-A c):=by
  rw [hDr,LinearMap.neg_apply,LinearMap.comp_apply,map_neg]
  rw [U8]
  rfl
 have hcu (c):aV (aO w u' c)=((B c).val,0):=by
  rw [hDu,LinearMap.comp_apply,U7,<- hE]
  simp [A]
 refine ⟨r',u',?_,hcr,hcu⟩
 rw [Oo,hN]
 simpa only [dH,Oo] using Oj (T:=I) v r hp
end RelatorBlocks
section Reindexing
variable {Γ S T U R I:Type*} [Group Γ]
def q9:I ⊕ (T ⊕ R) ≃ R ⊕ (I ⊕ T) where
 toFun
  | .inl i=>.inr (.inl i)
  | .inr (.inl t)=>.inr (.inr t)
  | .inr (.inr r)=>.inl r
 invFun
  | .inl r=>.inr (.inr r)
  | .inr (.inl i)=>.inl i
  | .inr (.inr t)=>.inr (.inl t)
 left_inv:=by rintro (i | (t | r)) <;> rfl
 right_inv:=by rintro (r | (i | t)) <;> rfl
end Reindexing
section ExtraProjectionAlignment
variable {Γ S T I R:Type*} [Group Γ]
omit [Group Γ] in
theorem U9 (c:aE Γ (S ⊕ T)) :
  bC c=(aV c).2:=by
 have h:bC=(LinearMap.snd ℤ _ _).comp
   (aV:aE Γ (S ⊕ T) ≃ₗ[ℤ] _).toLinearMap:=by
  apply Finsupp.lhom_ext
  rintro ⟨g,s | t⟩ n <;> simp
 exact LinearMap.congr_fun h c
def tJ (A:aE Γ R ≃ₗ[ℤ] aE Γ I) :
  aE Γ (T ⊕ R) ≃ₗ[ℤ] aE Γ (T ⊕ I):=
 aV.trans (((LinearEquiv.refl ℤ (aE Γ T)).prodCongr
  (A.trans (LinearEquiv.neg ℤ))).trans aV.symm)
end ExtraProjectionAlignment
section FinishedAlignment
variable {Γ S T R Z:Type*} [Group Γ]
private theorem qO {V W M:Type*} [AddCommGroup M] [Module ℤ M]
  (v:V → Γ) (w:W → Γ) (e:V ≃ W) (he:∀ s,w (e s)=v s)
  (N:aE Γ W →ₗ[ℤ] M) (O:aE Γ V →ₗ[ℤ] M)
  (gen:N.comp (aO w (fun s=>freeGroupCongr e (FreeGroup.of s)))=O)
  (p:R → FreeGroup V) (c:aE Γ R) :
  N (aO w (fun i=>freeGroupCongr e (p i)) c)=O (aO v p c):=by
 rw [← uZ v w _ (l8 v w e he)]
 exact LinearMap.congr_fun gen _
end FinishedAlignment
open scoped Quaternion
section BoundaryBasisTransport
variable {Γ S Z T R₀:Type*} [Group Γ] [Group.ResiduallyFinite Γ] [Fintype Z]
theorem Vc
  (v:S -> Γ) (hv:Function.Surjective (aD v))
  (z:Z -> FreeGroup S) (hz:∀ i,aD v (z i)=1)
  (B:aE Γ Z ≃ₗ[ℤ] cycles v)
  (hB:∀ c,(B c:aE Γ S)=aO v z c)
  (a₀:T -> Γ) (ha₀:Function.Surjective (aD a₀))
  (r₀:R₀ -> FreeGroup T) (_hr₀:∀ i,aD a₀ (r₀ i)=1)
(hp₀:(aD a₀).ker=Subgroup.normalClosure (Set.range r₀))
    (E:aE Γ R₀ ≃ₗ[ℤ] cycles a₀)
    (hE:∀ c,(E c:aE Γ T)=aO a₀ r₀ c) :
    ∃ η:ℝ,0 < η /\ ∀ a:Γ -> S -> a3,
      (∀ g s,‖(a g s:ℍ)-1‖ < η) ->
      (∀ i g,aR v a (z i) g=1) ->
      ∀ w:FreeGroup S,aD v w=1 -> ∀ g,
        aR v a w g=1:=by
  let P:=U6 v hv a₀ ha₀ (⟨r₀,hp₀,E,hE⟩:BasedPresentation a₀ R₀)
  let v₀:S ⊕ T -> Γ:=Sum.elim v (fun _=>1)
  let B₀:aE Γ (Z ⊕ T) ≃ₗ[ℤ] cycles v₀:=u5 v B
  let z₀:Z ⊕ T -> FreeGroup (S ⊕ T):=dH z
  have hB₀:∀ c,(B₀ c:aE Γ (S ⊕ T))=aO v₀ z₀ c:=
    Ol v z B hB
  obtain ⟨r,u,hp,hcr,hcu⟩:=zF v₀ (B9 v hv) P.rel z₀
    P.normal P.basis B₀ P.realizes hB₀
  let R:=R₀ ⊕ S
  let A:=P.basis.trans B₀.symm
  let w:=Sum.elim (Sum.elim v (fun _:T=>1)) (fun _:Z ⊕ T=>1)
  change ∀ c,aV (aO w r c)=(0,-A c) at hcr
  change ∀ c,aV (aO w u c)=((B₀ c).val,0) at hcu
  let w':=Sum.elim v (fun _:T ⊕ (Z ⊕ T)=>1)
  let e:=Equiv.sumAssoc S T (Z ⊕ T)
  let j:Z ⊕ (T ⊕ R) ≃ R ⊕ (Z ⊕ T):=q9
  have he:∀ s,w' (e s)=w s:=by rintro ((s | t) | i) <;> rfl
  let f:R ⊕ (Z ⊕ T) -> FreeGroup (S ⊕ (T ⊕ (Z ⊕ T))):=
    fun i=>freeGroupCongr e (Sum.elim r u i)
  let r':=f ∘ j
  have hpr:(aD w').ker=Subgroup.normalClosure (Set.range r'):=by
    rw [show Set.range r'=Set.range f from j.surjective.range_comp f]
    exact k2 w w' (freeGroupCongr e) (l8 w w' e he) _ hp
  let Q:=tJ (T:=T) A
  let old:aE Γ ((S ⊕ T) ⊕ (Z ⊕ T)) ≃ₗ[ℤ] _:=
    aV.trans (aV.prodCongr (LinearEquiv.refl ℤ _))
  let new:=(aV (Γ:=Γ) (S:=S) (T:=T ⊕ (Z ⊕ T))).trans
    (((LinearEquiv.refl ℤ _).prodCongr aV).trans (LinearEquiv.prodAssoc ℤ _ _ _).symm)
  have gen:new.toLinearMap.comp (aO w' (fun s=>freeGroupCongr e (FreeGroup.of s))) = old.toLinearMap:=by
    apply Finsupp.lhom_ext
    rintro ⟨g,(s | t) | i⟩ n <;> simp [new,old,e,Equiv.sumAssoc] <;> rfl
  have basisCoord (c:aE Γ (Z ⊕ T)) :
      aV (B₀ c).val = ((B (aV c).1).val,(aV c).2):=
    aV.apply_symm_apply _
  let D:=(B.toLinearMap.prodMap Q.toLinearMap).comp aV.toLinearMap
  have h:(aV.toLinearMap.comp (aO w' r')) =
      ((cycles v).subtype.prodMap LinearMap.id).comp D:=by
    apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    apply ((LinearEquiv.refl ℤ (aE Γ S)).prodCongr
      (aV (S:=T) (T:=Z ⊕ T))).injective
    have assoc (x:aE Γ S × aE Γ T) (y:aE Γ (Z ⊕ T)) :
        LinearEquiv.prodAssoc ℤ _ _ _ (x,y) = (x.1,x.2,y):=rfl
    rcases i with z | (t | k) <;> first
      | have h:=qO w w' e he _ _ gen u (Finsupp.single (g,Sum.inl z) n)
      | have h:=qO w w' e he _ _ gen u (Finsupp.single (g,Sum.inr t) n)
      | have h:=qO w w' e he _ _ gen r (Finsupp.single (g,k) n)
    all_goals
      have h:=congrArg (LinearEquiv.prodAssoc ℤ _ _ _) h
      simp only [LinearEquiv.coe_coe,new,old,LinearEquiv.trans_apply,LinearEquiv.apply_symm_apply,
        LinearEquiv.prodCongr_apply,LinearEquiv.refl_apply,hcu,hcr,basisCoord] at h
      simpa [D,Q,tJ,r',f,j,q9,assoc] using h
  have diagram (c:aE Γ (Z ⊕ (T ⊕ R))) :
      aV (aO w' r' c) =
        ((B (aV c).1).val,Q (aV c).2):=LinearMap.congr_fun h c
  refine UK w' r' z (fun _=>rfl) (rV hpr) hz hpr ?_ ?_ Q ?_
  · intro c d h
    have p:=(diagram c).symm.trans ((congrArg aV h).trans (diagram d))
    exact aV.injective (Prod.ext (B.injective (Subtype.ext (congrArg Prod.fst p)))
      (Q.injective (congrArg Prod.snd p)))
  · intro i
    apply aV.injective
    simpa [w',LD,hB] using (diagram (Finsupp.single (1,Sum.inl i) 1)).symm
  · apply Finsupp.lhom_ext
    rintro ⟨g,i⟩ n
    simpa [U9] using (congrArg Prod.snd (diagram (Finsupp.single (g,Sum.inr i) n))).symm
end BoundaryBasisTransport
end EilenbergGanea
end
noncomputable section
open Classical Set
namespace EilenbergGanea
open CategoryTheory
section ProjectiveBound
variable {R P Q M:Type} [Ring R]
 [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
 [AddCommGroup M] [Module R M]
theorem Vd
  (ε:P →ₗ[R] M) (hε:Function.Surjective ε)
  (d:Q →ₗ[R] LinearMap.ker ε) (hd:Function.Surjective d)
  [Module.Projective R P] [Module.Projective R Q]
  [Module.Projective R (LinearMap.ker d)] :
  CategoryTheory.projectiveDimension (ModuleCat.of R M) <= 2:=by
 have h₁:=(LinearMap.shortExact_shortComplexKer hd).hasProjectiveDimensionLT_X₃ 1
  (inferInstance:HasProjectiveDimensionLT (ModuleCat.of R (LinearMap.ker d)) 1)
  (inferInstance:HasProjectiveDimensionLT (ModuleCat.of R Q) 2)
 have h₂:=(LinearMap.shortExact_shortComplexKer hε).hasProjectiveDimensionLT_X₃ 2
  h₁ (inferInstance:HasProjectiveDimensionLT (ModuleCat.of R P) 3)
 exact (CategoryTheory.projectiveDimension_le_iff _ 2).mpr h₂
end ProjectiveBound
section CayleyModules
variable {Γ S:Type} [Group Γ]
abbrev a7 (Γ:Type) [Group Γ]:=MonoidAlgebra ℤ Γ
abbrev p3 (Γ:Type) [Group Γ]:=
 (Representation.trivial ℤ Γ ℤ).asModule
def e3:a7 Γ →ₗ[a7 Γ] p3 Γ:=
 LinearMap.toSpanSingleton (a7 Γ) _
  ((Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1)
@[simp] theorem l1 (g:Γ) (n:ℤ) :
  e3 (MonoidAlgebra.single g n) =
   (Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm n:=by
 change (MonoidAlgebra.single g n:a7 Γ) •
  ((Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1)=_
 rw [Representation.single_smul]
 change (n:ℤ) * 1=n
 exact mul_one n
theorem Ve :
  Function.Surjective (e3 (Γ:=Γ)):=by
 intro n
 refine ⟨MonoidAlgebra.single (1:Γ) ((Representation.trivial ℤ Γ ℤ).asModuleEquiv n),?_⟩
 rw [l1,LinearEquiv.symm_apply_apply]
def bU (v:S -> Γ) :
  (S →₀ a7 Γ) →ₗ[a7 Γ] a7 Γ:=
 Finsupp.linearCombination _ (fun s=>MonoidAlgebra.single (v s) 1 - 1)
@[simp] theorem Vf (v:S -> Γ) (s:S) (r:a7 Γ) :
  bU v (Finsupp.single s r)=r * (MonoidAlgebra.single (v s) 1 - 1):=by
 simp [bU]
@[simp] theorem Vg :
  e3 (1:a7 Γ) =
   (Representation.trivial ℤ Γ ℤ).asModuleEquiv.symm 1:=
 l1 (1:Γ) 1
@[simp] theorem Vh (g:Γ) :
  e3 (MonoidAlgebra.single g 1 - 1)=0:=by
 rw [map_sub,l1,Vg,sub_self]
theorem Oq (v:S -> Γ) :
    (e3 (Γ:=Γ)).comp (bU v)=0:=by
  change (e3 (Γ:=Γ)).comp
    (Finsupp.linearCombination _ (fun s=>MonoidAlgebra.single (v s) 1 - 1))=0
  rw [<- Finsupp.linearCombination_linear_comp]
  have he:(e3 (Γ:=Γ)) ∘
      (fun s=>MonoidAlgebra.single (v s) 1 - 1)=(0:S -> p3 Γ):=by
    funext s
    exact Vh (v s)
  rw [he,Finsupp.linearCombination_zero]
 theorem q6 (v:S -> Γ) (w:FreeGroup S) :
    MonoidAlgebra.single (FreeGroup.lift v w) 1 - 1 ∈ LinearMap.range (bU v):=by
  induction w using FreeGroup.induction_on with
  | C1=>
      simp only [map_one]
      have he:(MonoidAlgebra.single (1:Γ) 1:a7 Γ)=1:=rfl
      rw [he,sub_self]
      exact Submodule.zero_mem _
  | of s=>
      exact ⟨Finsupp.single s 1,by simp⟩
  | inv_of s=>
      refine ⟨Finsupp.single s (-MonoidAlgebra.single (v s)⁻¹ 1),?_⟩
      simp [mul_sub,MonoidAlgebra.single_mul_single]
      rfl
  | mul w z hw hz=>
      have hh:=(LinearMap.range (bU v)).smul_mem
        (MonoidAlgebra.single (FreeGroup.lift v w) 1) hz
      have hc:=(LinearMap.range (bU v)).add_mem hw hh
      rw [map_mul]
      convert hc using 1
      change _=(_ - 1) + _ * (_ - 1)
      rw [mul_sub,mul_one,MonoidAlgebra.single_mul_single,one_mul]
      abel
theorem rJ (v:S -> Γ)
  (hv:Function.Surjective (FreeGroup.lift v)) (r:a7 Γ) :
  r - MonoidAlgebra.single 1
   ((Representation.trivial ℤ Γ ℤ).asModuleEquiv (e3 r)) ∈
    LinearMap.range (bU v):=by
 classical
 induction r using MonoidAlgebra.induction_linear with
 | zero=>simp
 | add r t hr ht=>
   rw [map_add,map_add,MonoidAlgebra.single_add]
   convert (LinearMap.range (bU v)).add_mem hr ht using 1; abel
 | single g n=>
   rw [l1,LinearEquiv.apply_symm_apply]
   obtain ⟨w,hw⟩:=hv g
   have hm:=(LinearMap.range (bU v)).toAddSubgroup.zsmul_mem
    (q6 v w) n
   rw [hw] at hm
   convert hm using 1
   simp only [smul_sub,MonoidAlgebra.smul_single,zsmul_eq_mul,mul_one]
   rfl
theorem Vi (v:S -> Γ) (hv:Function.Surjective (FreeGroup.lift v)) :
  LinearMap.range (bU v)=LinearMap.ker (e3 (Γ:=Γ)):=by
 apply le_antisymm
 ·rintro _ ⟨r,rfl⟩
  exact LinearMap.congr_fun (Oq v) r
 ·intro r hr
  have hm:=rJ v hv r
  rw [LinearMap.mem_ker.mp hr,map_zero,MonoidAlgebra.single_zero,sub_zero] at hm
  exact hm
def jZ (v:S -> Γ) :
  (S →₀ a7 Γ) →ₗ[a7 Γ]
   LinearMap.ker (e3 (Γ:=Γ)):=
 (bU v).codRestrict _ (by
  intro r
  exact LinearMap.congr_fun (Oq v) r)
theorem Vk (v:S -> Γ)
  (hv:Function.Surjective (FreeGroup.lift v)) :
  Function.Surjective (jZ v):=by
 intro r
 have hr:(r:a7 Γ) ∈ LinearMap.range (bU v):=by
  rw [Vi v hv]
  exact r.property
 obtain ⟨s,hs⟩:=hr
 exact ⟨s,Subtype.ext hs⟩
theorem Vm (v:S -> Γ)
  (hv:Function.Surjective (FreeGroup.lift v))
  [Module.Projective (a7 Γ) (LinearMap.ker (bU v))] :
  CategoryTheory.projectiveDimension
   (ModuleCat.of (a7 Γ) (p3 Γ)) <= 2:=by
 have hk:LinearMap.ker (jZ v) =
   LinearMap.ker (bU v):=LinearMap.ker_codRestrict _ _ _
 have:Module.Projective (a7 Γ)
   (LinearMap.ker (jZ v)):=hk ▸ inferInstance
 exact Vd e3
  Ve (jZ v)
  (Vk v hv)
end CayleyModules
end EilenbergGanea
namespace EilenbergGanea
section ChainPackaging
variable {Γ S T:Type} [Group Γ]
def bD:aE Γ S ≃ₗ[ℤ] S →₀ a7 Γ:=
 ((Finsupp.domLCongr (Equiv.prodComm Γ S)).trans (Finsupp.curryLinearEquiv ℤ)).trans
  (Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv ℤ).symm)
@[simp] theorem Vq (g:Γ) (s:S) (n:ℤ) :
  bD (Finsupp.single (g,s) n) =
   Finsupp.single s (MonoidAlgebra.single g n):=by
 simp [bD,Finsupp.curry_single]
@[simp] theorem df2 (g:Γ) (s:S) (n:ℤ) :
  (bD (Γ:=Γ) (S:=S)).symm
    (Finsupp.single s (MonoidAlgebra.single g n))=Finsupp.single (g,s) n:=by
 apply (bD (Γ:=Γ) (S:=S)).injective
 simp
theorem Ot (g:Γ) (c:aE Γ S) :
  bD (aZ g c) =
   (MonoidAlgebra.single g 1:a7 Γ) • bD c:=by
 have he:(bD (Γ:=Γ) (S:=S)).toLinearMap.comp (aZ g) =
   (DistribSMul.toLinearMap ℤ (S →₀ a7 Γ) (MonoidAlgebra.single g 1:a7 Γ)).comp
    (bD (Γ:=Γ) (S:=S)).toLinearMap:=by
  apply Finsupp.lhom_ext
  rintro ⟨h,s⟩ n
  simp [Finsupp.smul_single,MonoidAlgebra.single_mul_single]
 exact LinearMap.congr_fun he c
theorem Vr (v:S -> Γ) (c:aE Γ S) :
    bU v (bD c)=MonoidAlgebra.ofCoeff (bY v c):=by
  have he:((bU v).restrictScalars ℤ).comp
      (bD (Γ:=Γ) (S:=S)).toLinearMap =
      (MonoidAlgebra.coeffLinearEquiv ℤ).symm.toLinearMap.comp (bY v):=by
    apply Finsupp.lhom_ext
    rintro ⟨g,s⟩ n
    simp only [LinearMap.comp_apply,LinearMap.coe_restrictScalars,LinearEquiv.coe_coe,
      Vq,Vf,Od,map_smul,
      map_sub]
    simp only [mul_sub,MonoidAlgebra.single_mul_single,mul_one,
      MonoidAlgebra.coeffLinearEquiv_symm_apply,MonoidAlgebra.ofCoeff_single,
      MonoidAlgebra.smul_single,smul_sub,smul_eq_mul]
  exact LinearMap.congr_fun he c
theorem Vt (g:Γ) (c:S →₀ a7 Γ) :
  (bD (Γ:=Γ) (S:=S)).symm ((MonoidAlgebra.single g 1:a7 Γ) • c) =
   aZ g (bD.symm c):=by
 apply (bD (Γ:=Γ) (S:=S)).injective
 rw [Ot,LinearEquiv.apply_symm_apply,LinearEquiv.apply_symm_apply]
def vY (A:aE Γ S →ₗ[ℤ] aE Γ T)
  (hA:b8 A) :
  (S →₀ a7 Γ) →ₗ[a7 Γ] T →₀ a7 Γ where
 toFun c:=bD (A (bD.symm c))
 map_add' _ _:=by simp only [map_add]
 map_smul' r c:=by
  induction r using MonoidAlgebra.induction_linear with
  | zero=>simp only [zero_smul,map_zero]
  | add r t hr ht=>simp only [add_smul,map_add,hr,ht]
  | single g n=>
    have hn:(MonoidAlgebra.single g n:a7 Γ) =
      n • MonoidAlgebra.single g 1:=by simp
    rw [hn]
    simp only [smul_assoc,map_smul,Vt,RingHom.id_apply]
    rw [hA g _,Ot]
@[simp] theorem dq1 (A:aE Γ S →ₗ[ℤ] aE Γ T)
  (hA:b8 A) (c:S →₀ a7 Γ) :
  vY A hA c=bD (A (bD.symm c)):=rfl
theorem Ou (v:S -> Γ) (c:aE Γ S) :
  c ∈ cycles v ↔ bD c ∈ LinearMap.ker (bU v):=by
 change bY v c=0 ↔ bU v (bD c)=0
 rw [Vr]
 constructor
 ·intro h
  rw [h]
  rfl
 ·intro h
  have hh:=congrArg MonoidAlgebra.coeff h
  exact hh
theorem y6 (v:S -> Γ)
  (A:aE Γ T →ₗ[ℤ] aE Γ S) (hA:b8 A)
  (hAi:Function.Injective A) (hAr:LinearMap.range A=cycles v) :
  Module.Projective (a7 Γ) (LinearMap.ker (bU v)):=by
 have hm:∀ c,vY A hA c ∈ LinearMap.ker (bU v):=by
  intro c
  apply (Ou v _).mp
  rw [<- hAr]
  exact ⟨bD.symm c,rfl⟩
 let d:=(vY A hA).codRestrict _ hm
 have hi:Function.Injective d:=by
  intro c c' h
  apply (bD (Γ:=Γ) (S:=T)).symm.injective
  apply hAi
  apply bD.injective
  exact congrArg Subtype.val h
 have hs:Function.Surjective d:=by
  intro c
  have hc:bD.symm (c:S →₀ a7 Γ) ∈ cycles v:=by
   apply (Ou v _).mpr
   rw [LinearEquiv.apply_symm_apply]
   exact c.property
  rw [<- hAr] at hc
  obtain ⟨b,hb⟩:=hc
  refine ⟨bD b,Subtype.ext ?_⟩
  change bD (A (bD.symm (bD b)))=c.val
  rw [LinearEquiv.symm_apply_apply,hb,LinearEquiv.apply_symm_apply]
 exact Module.Projective.of_equiv' (LinearEquiv.ofBijective d ⟨hi,hs⟩)
theorem w4 (v:S -> Γ)
  (hv:Function.Surjective (FreeGroup.lift v))
  (A:aE Γ T →ₗ[ℤ] aE Γ S) (hA:b8 A)
  (hAi:Function.Injective A) (hAr:LinearMap.range A=cycles v) :
  CategoryTheory.projectiveDimension
   (ModuleCat.of (a7 Γ) (p3 Γ)) <= 2:=by
 have:=y6 v A hA hAi hAr
 exact Vm v hv
end ChainPackaging
end EilenbergGanea
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea
namespace AffineTransport
theorem pU {A V:Type*} [Finite A] [Fintype V]
  (T:A -> V -> ℍ ≃ₗ[ℝ] ℍ) :
  ∃ q:V -> ℍ,∀ a (s:Finset V),s.card <= 3 ->
   LinearIndepOn ℝ (fun v=>T a v (q v)) (s:Set V):=by
 classical
 let I:=A × {s:Finset V // s.card ≤ 3}
 let good (i:I):={q:V → ℍ | LinearIndepOn ℝ (fun v=>T i.1 v (q v)) (i.2.val:Set V)}
 suffices ∀ i,∃ U:Set (V → ℍ),IsOpen U ∧ Dense U ∧ U ⊆ good i by
  choose U ho hd hsub using this
  obtain ⟨q,hq⟩:=(dense_iInter_of_isOpen ho hd).nonempty
  exact ⟨q,fun a s hs=>hsub (a,⟨s,hs⟩) (mem_iInter.mp hq _)⟩
 rintro ⟨a,s,hs⟩
 obtain ⟨e⟩:=Function.Embedding.nonempty_of_card_le (α:=↥s) (β:=Fin 4)
  (by simpa using (show s.card ≤ 4 by omega))
 let b:Module.Basis (Fin 4) ℝ ℍ:=QuaternionAlgebra.basisOneIJK _ _ _
 let L:ℍ →ₗ[ℝ] (s → ℝ):=LinearMap.pi fun j=>b.coord (e j)
 let M (q:V → ℍ):Matrix s s ℝ:=fun i=>L (T a i (q i))
 let d (q:V → ℍ):=(M q).det
 have ha:AnalyticOnNhd ℝ d univ:=by
  intro q _
  change AnalyticAt ℝ (fun p=>(M p).det) q
  simp_rw [Matrix.det_apply']
  apply Finset.analyticAt_fun_sum
  intro σ _
  apply AnalyticAt.mul analyticAt_const
  apply Finset.analyticAt_fun_prod
  intro i _
  exact (((b.coord (e i)).comp ((T a (σ i)).toLinearMap.comp
   (LinearMap.proj (R:=ℝ) (φ:=fun _:V=>ℍ) (σ i:V)))).toContinuousLinearMap).analyticAt q
 let q₀ (v:V):=if h:v ∈ s then (T a v).symm (b (e ⟨v,h⟩)) else 0
 have h₀:M q₀ = 1:=by
  ext i j
  simp [M,L,q₀,i.property,Module.Basis.coord_apply,Matrix.one_apply,Finsupp.single_apply]
 refine ⟨{q | d q ≠ 0},isOpen_ne_fun (continuous_iff_continuousAt.mpr fun q=>(ha q trivial).continuousAt) continuous_const,?_,?_⟩
 ·apply dense_iff_inter_open.mpr
  rintro U hU ⟨x,hx⟩
  by_contra h
  have hz:d =ᶠ[𝓝 x] 0:=Filter.mem_of_superset (hU.mem_nhds hx) fun y hy=>by
   by_contra hn
   exact h ⟨y,hy,hn⟩
  have he:=ha.eq_of_eventuallyEq analyticOnNhd_const hz
  have hz₀:d q₀ = 0:=congrFun he q₀
  simp [d,h₀] at hz₀
 ·intro q hq
  exact LinearIndependent.of_comp L (Matrix.linearIndependent_rows_of_det_ne_zero hq)
@[simp] theorem Ov (h:a3):‖(h:ℍ)‖=1:=
 (c9 _).mp h.property
def qP (h:a3):ℍ ≃ₗ[ℝ] ℍ where
 toFun q:=(h:ℍ) * q
 invFun q:=(h⁻¹:a3) * q
 left_inv q:=by simp [<- mul_assoc,<- Submonoid.coe_mul]
 right_inv q:=by simp [<- mul_assoc,<- Submonoid.coe_mul]
 map_add' _ _:=mul_add _ _ _
 map_smul' r q:=mul_smul_comm r (h:ℍ) q
@[simp] theorem dl4 (h:a3) (q:ℍ) :
  qP h q=(h:ℍ) * q:=rfl
theorem Vv (h:a3) {q:ℍ} (hq:q ≠ 0) :
  bT ((h:ℍ) * q)=h * bT q:=by
 have hh:(h:ℍ) * q ≠ 0:=by
  exact (qP h).map_ne_zero_iff.mpr hq
 apply Subtype.ext
 rw [c1 hh]
 change ‖(h:ℍ) * q‖⁻¹ • ((h:ℍ) * q)=(h:ℍ) * (bT q:ℍ)
 rw [c1 hq,norm_mul,Ov,one_mul,mul_smul_comm]
section FiniteSimplex
variable {V:Type*} [Fintype V]
def x7:Set (V -> ℝ):=
 {weights | (∀ vertex,0 <= weights vertex) /\ ∑ vertex,weights vertex=1}
def face (s:Finset V):Set (V -> ℝ):=
 {b | b ∈ x7 /\ ∀ v ∉ s,b v=0}
def rW:Set (V -> ℝ):=
 ⋃ s:{s:Finset V // s.card <= 3},face s.val
abbrev b0 (V:Type*) [Fintype V]:=(rW:Set (V -> ℝ))
theorem oD {b:V -> ℝ}:b ∈ rW ↔
  ∃ s:Finset V,s.card <= 3 /\ b ∈ x7 /\ ∀ v ∉ s,b v=0:=by
 simp only [rW,Set.mem_iUnion,face,Set.mem_ofPred_eq,Subtype.exists,exists_prop]
omit [Fintype V] in
private theorem Vw (s:Finset V) :
  IsClosed {b:V -> ℝ | ∀ v ∉ s,b v=0}:=by
 have he:{b:V -> ℝ | ∀ v ∉ s,b v=0} =
   ⋂ v,⋂ (_:v ∉ s),{b:V -> ℝ | b v=0}:=by ext b; simp
 rw [he]
 exact isClosed_iInter fun v=>isClosed_iInter fun _=>
  isClosed_eq (continuous_apply v) continuous_const
theorem Vz (s:Finset V):IsCompact (face s):=by
 have compact_simplex:IsCompact (x7:Set (V -> ℝ)):=by
  exact isCompact_stdSimplex ℝ V
 exact compact_simplex.inter_right (Vw s)
theorem VA:IsCompact (rW:Set (V -> ℝ)):=
 isCompact_iUnion fun _=>Vz _
instance:CompactSpace (b0 V):=
 isCompact_iff_compactSpace.mp VA
theorem LG (b:b0 V):(b:V -> ℝ) ∈ x7:=by
 obtain ⟨_,_,h,_⟩:=oD.mp b.property
 exact h
theorem Ow (b:b0 V):∃ v,(b:V -> ℝ) v ≠ 0:=by
 by_contra! h
 have he:=(LG b).2
 simp only [h,Finset.sum_const_zero] at he
 norm_num at he
variable (h:V -> V -> a3) (q:V -> ℍ)
def pW (a:V) (b:V -> ℝ):ℍ:=∑ v,b v • ((h a v:ℍ) * q v)
def c2:Prop:=∀ a (s:Finset V),s.card <= 3 ->
 LinearIndepOn ℝ (fun v=>(h a v:ℍ) * q v) (s:Set V)
theorem VE:∃ q:V -> ℍ,c2 h q:=by
 obtain ⟨q,hq⟩:=pU (fun a v=>qP (h a v))
 exact ⟨q,hq⟩
theorem Ox (hq:c2 h q) (a:V) (b:b0 V) :
  pW h q a b ≠ 0:=by
 classical
 obtain ⟨s,hs,hb,hout⟩:=oD.mp b.property
 intro he
 have he':∑ v ∈ s,(b:V -> ℝ) v • ((h a v:ℍ) * q v)=0:=by
  rw [<- he]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro v _ hv
  rw [hout v hv,zero_smul]
 have hz:=(linearIndepOn_iff'.mp (hq a s hs)) s b (Set.Subset.refl _) he'
 have hall:∀ v,(b:V -> ℝ) v=0:=by
  intro v
  by_cases hv:v ∈ s
  ·exact hz v hv
  ·exact hout v hv
 have heq:=hb.2
 simp only [hall,Finset.sum_const_zero] at heq
 norm_num at heq
def gauge (a:V) (b:b0 V):a3:=bT (pW h q a b)
theorem VF (a:V):Continuous (pW h q a):=
 continuous_finsetSum _ fun v _=>(continuous_apply v).smul continuous_const
theorem continuous_gauge (hq:c2 h q) (a:V):Continuous (gauge h q a):=by
 apply continuous_iff_continuousAt.mpr
 intro b
 exact ContinuousAt.comp (f:=fun c:b0 V=>pW h q a c)
  (SO (Ox h q hq a b))
  ((VF h q a).comp continuous_subtype_val).continuousAt
theorem VJ (hq:c2 h q) {ε:ℝ} (hε:0 < ε) :
  ∃ δ > 0,∀ b c:b0 V,dist b c < δ ->
   ∀ a,dist (gauge h q a b) (gauge h q a c) < ε:=by
 have hc:Continuous (fun b:b0 V=>fun a=>gauge h q a b):=
  continuous_pi fun a=>continuous_gauge h q hq a
 have hu:=CompactSpace.uniformContinuous_of_continuous hc
 obtain ⟨δ,hδ,H⟩:=Metric.uniformContinuous_iff.mp hu ε hε
 refine ⟨δ,hδ,?_⟩
 intro b c hbc a
 exact lt_of_le_of_lt (dist_le_pi_dist (fun a=>gauge h q a b) (fun a=>gauge h q a c) a) (H hbc)
end FiniteSimplex
theorem Oy (a b c:a3):dist (a * b) (a * c)=dist b c:=by
 change dist ((a:ℍ) * (b:ℍ)) ((a:ℍ) * (c:ℍ))=dist (b:ℍ) (c:ℍ)
 rw [dist_eq_norm,dist_eq_norm,<- mul_sub,norm_mul,Ov,one_mul]
theorem VK (a b:a3):dist (a⁻¹ * b) 1=dist a b:=by
 rw [<- Oy a (a⁻¹ * b) 1]
 simp [dist_comm]
theorem VN (a b:a3) :
  dist (a * b) 1 <= dist a 1 + dist b 1:=by
 calc
  dist (a * b) 1 <= dist (a * b) a + dist a 1:=dist_triangle _ _ _
  _=dist b 1 + dist a 1:=by
   exact congrArg (fun t=>t + dist a 1) (by simpa only [mul_one] using Oy a b 1)
  _=dist a 1 + dist b 1:=add_comm _ _
section Connection
variable {V:Type*} [Fintype V]
variable (L:SimpleGraph V)
def g4 (a b:V):Prop:=a=b \/ L.Adj a b
omit [Fintype V] in
theorem g4.refl (a:V):g4 L a a:=Or.inl rfl
def Star (a:V) (b:b0 V):Prop:=
 ∀ v,(b:V -> ℝ) v ≠ 0 -> g4 L a v
def o0 (b:b0 V):Prop:=
 ∀ a,(b:V -> ℝ) a ≠ 0 -> Star L a b
def Compatible (b c:b0 V):Prop:=
 ∀ v w,((b:V -> ℝ) v ≠ 0 \/ (c:V -> ℝ) v ≠ 0) ->
  ((b:V -> ℝ) w ≠ 0 \/ (c:V -> ℝ) w ≠ 0) -> g4 L v w
def root (b:b0 V):V:=Classical.choose (Ow b)
theorem Ju (b:b0 V):(b:V -> ℝ) (root b) ≠ 0:=
 Classical.choose_spec (Ow b)
variable (h:V -> V -> a3) (q:V -> ℍ)
def d7:Prop:=∀ a b c,g4 L a b -> g4 L b c ->
 g4 L a c -> h a b * h b c=h a c
theorem VO (hf:d7 L h) {a c:V}
  {b:b0 V} (hac:g4 L a c) (ha:Star L a b) (hc:Star L c b) :
  pW h q a b=(h a c:ℍ) * pW h q c b:=by
 classical
 simp only [pW,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro v _
 by_cases hv:(b:V -> ℝ) v=0
 ·simp [hv]
 ·rw [mul_smul_comm,<- mul_assoc,<- Submonoid.coe_mul,hf a c v hac (hc v hv) (ha v hv)]
theorem LI (hf:d7 L h) (hq:c2 h q)
  {a c:V} {b:b0 V} (hac:g4 L a c)
  (ha:Star L a b) (hc:Star L c b) :
  gauge h q a b=h a c * gauge h q c b:=by
 unfold gauge
 rw [VO L h q hf hac ha hc]
 exact Vv _ (Ox h q hq c b)
def dY (a:V) (b c:b0 V):a3:=
 (gauge h q a b)⁻¹ * gauge h q a c
def transport (b c:b0 V):a3:=dY h q (root b) b c
theorem qQ (hf:d7 L h) (hq:c2 h q)
    {b c:b0 V} (hb:Compatible L b c) {a:V}
    (hab:Star L a b) (hac:Star L a c) :
    transport h q b c=dY h q a b c:=by
  have hrb:Star L (root b) b:=fun v hv=>hb _ _ (Or.inl (Ju b)) (Or.inl hv)
  have hrc:Star L (root b) c:=fun v hv=>hb _ _ (Or.inl (Ju b)) (Or.inr hv)
  have har:g4 L a (root b):=hab _ (Ju b)
  unfold transport dY
  rw [LI L h q hf hq har hab hrb,
    LI L h q hf hq har hac hrc]
  group
theorem p0 {b c:b0 V} (hb:Compatible L b c) :
  Compatible L c b:=fun v w hv hw=>hb v w hv.symm hw.symm
theorem u7 (hf:d7 L h) (hq:c2 h q)
  {b c:b0 V} (hb:Compatible L b c) :
  transport h q c b=(transport h q b c)⁻¹:=by
 have hrc:Star L (root b) c:=fun v hv=>hb _ _ (Or.inl (Ju b)) (Or.inr hv)
 have hrb:Star L (root b) b:=fun v hv=>hb _ _ (Or.inl (Ju b)) (Or.inl hv)
 rw [qQ L h q hf hq (p0 L hb) hrc hrb]
 unfold transport dY
 group
theorem qU (a:V) (b c d:b0 V) :
  dY h q a b c * dY h q a c d=dY h q a b d:=by
 unfold dY
 group
theorem VT (b:b0 V) :
  ∃ a,1 / (Fintype.card V + 1:ℝ) < (b:V -> ℝ) a:=by
 by_contra! H
 have hs:=Finset.sum_le_sum (s:=Finset.univ) (fun a _=>H a)
 have hb:=(LG b).2
 rw [hb,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hs
 have hn:0 <= (Fintype.card V:ℝ):=Nat.cast_nonneg _
 have hd:0 < (Fintype.card V:ℝ) + 1:=by positivity
 have he:=(le_div_iff₀ hd).mp (by simpa only [mul_one_div] using hs)
 linarith
theorem w3 {b c:b0 V} {a:V}
  (ha:1 / (Fintype.card V + 1:ℝ) < (b:V -> ℝ) a)
  (hc:o0 L c) (hbc:dist b c < 1 / (Fintype.card V + 1:ℝ)) :
  Star L a c:=by
 apply hc a
 intro he
 have hd:=lt_of_le_of_lt (dist_le_pi_dist (b:V -> ℝ) (c:V -> ℝ) a) hbc
 rw [he,Real.dist_eq,sub_zero,abs_of_nonneg ((LG b).1 a)] at hd
 exact (not_lt_of_ge ha.le) hd
theorem VY (a:V) (b c:b0 V) :
  dist (dY h q a b c) 1=dist (gauge h q a b) (gauge h q a c):=
 VK _ _
theorem VZ (hq:c2 h q) {ε:ℝ} (hε:0 < ε) :
  ∃ δ > 0,∀ b c:b0 V,dist b c < δ -> dist (transport h q b c) 1 < ε:=by
 obtain ⟨δ,hδ,H⟩:=VJ h q hq hε
 exact ⟨δ,hδ,fun b c hbc=>(VY h q _ b c).symm ▸ H b c hbc (root b)⟩
def fF (b c d:b0 V):a3:=transport h q b c * transport h q c d
theorem s8 (hf:d7 L h) (hq:c2 h q)
    {b c d:b0 V} (hbc:Compatible L b c) (hcd:Compatible L c d)
    {a:V} (hab:Star L a b) (hac:Star L a c) (had:Star L a d) :
    fF h q b c d=dY h q a b d:=by
  rw [fF,qQ L h q hf hq hbc hab hac,
    qQ L h q hf hq hcd hac had,qU]
theorem V0 (hf:d7 L h) (hq:c2 h q)
    {b c d:b0 V} (hbc:Compatible L b c) (hcd:Compatible L c d) :
    fF h q d c b=(fF h q b c d)⁻¹:=by
  rw [fF,fF,u7 L h q hf hq hbc,
    u7 L h q hf hq hcd,mul_inv_rev]
theorem V5 (hq:c2 h q) {ε:ℝ} (hε:0 < ε) :
  ∃ δ > 0,∀ b c d:b0 V,dist b c < δ -> dist c d < δ ->
   dist (fF h q b c d) 1 < ε:=by
 obtain ⟨δ,hδ,H⟩:=VZ h q hq (show 0 < ε/2 by positivity)
 refine ⟨δ,hδ,?_⟩
 intro b c d hbc hcd
 apply lt_of_le_of_lt (VN _ _)
 have h₁:=H b c hbc
 have h₂:=H c d hcd
 linarith
theorem wY (hf:d7 L h) (hq:c2 h q)
    (b c d u v w:b0 V) {a:V}
    (hbu:Compatible L b u) (huc:Compatible L u c)
    (hcv:Compatible L c v) (hvd:Compatible L v d)
    (hdw:Compatible L d w) (hwb:Compatible L w b)
    (hab:Star L a b) (hac:Star L a c) (had:Star L a d)
    (hau:Star L a u) (hav:Star L a v) (haw:Star L a w) :
    fF h q b u c * fF h q c v d * fF h q d w b=1:=by
  rw [s8 L h q hf hq hbu huc hab hau hac,
    s8 L h q hf hq hcv hvd hac hav had,
    s8 L h q hf hq hdw hwb had haw hab]
  unfold dY
  group
end Connection
end AffineTransport
end EilenbergGanea
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
open scoped Quaternion
namespace EilenbergGanea
abbrev z5:=unitary ℍ
def seedGoldenReal:ℝ:=(1 + Real.sqrt 5) / 4
def seedXQuaternion:ℍ:=⟨0,1,0,0⟩
def seedYQuaternion:ℍ:=
 ⟨seedGoldenReal,1/2,Real.sqrt ((3 - Real.sqrt 5)/8),0⟩
theorem V6:4 * seedGoldenReal ^ 2 - 2 * seedGoldenReal - 1=0:=by
 have h:=Real.sq_sqrt (show (0:ℝ) <= 5 by norm_num)
 dsimp [seedGoldenReal]
 nlinarith
theorem LJ:Quaternion.normSq seedXQuaternion=1:=by
 rw [Quaternion.normSq_def']
 norm_num [seedXQuaternion]
theorem LL:Quaternion.normSq seedYQuaternion=1:=by
 have hs:=Real.sq_sqrt (show (0:ℝ) <= 5 by norm_num)
 have hn:=Real.sqrt_nonneg (5:ℝ)
 have hle:Real.sqrt (5:ℝ) <= 3:=by nlinarith
 have hc:=Real.sq_sqrt (show (0:ℝ) <= (3 - Real.sqrt 5)/8 by positivity)
 rw [Quaternion.normSq_def']
 change seedGoldenReal ^ 2 + (1 / 2:ℝ) ^ 2 + Real.sqrt ((3 - Real.sqrt 5)/8) ^ 2 + 0 ^ 2=1
 dsimp [seedGoldenReal]
 nlinarith
def seedXUnit:z5:=⟨seedXQuaternion,by
 rw [Unitary.mem_iff,Quaternion.star_mul_self,Quaternion.self_mul_star,LJ]
 simp⟩
def seedYUnit:z5:=⟨seedYQuaternion,by
 rw [Unitary.mem_iff,Quaternion.star_mul_self,Quaternion.self_mul_star,LL]
 simp⟩
theorem LO (q:ℍ) (h:Quaternion.normSq q=1) :
  q ^ 2=(2 * q.re:ℝ) * q - 1:=by
 have hh:=Quaternion.star_mul_self q
 rw [h,Quaternion.star_eq_two_re_sub,sub_mul] at hh
 simp only [Quaternion.coe_one] at hh
 have hh':((2 * q.re:ℝ):ℍ) * q=1 + q * q:=by
  simpa only [add_comm] using sub_eq_iff_eq_add.mp hh
 rw [pow_two]
 apply eq_sub_iff_add_eq.mpr
 simpa only [add_comm] using hh'.symm
open Polynomial in
theorem vZ (q:ℍ) (h:Quaternion.normSq q=1)
  (hr:q.re=1/2):q ^ 3=-1:=by
 have hh:=LO q h
 rw [hr] at hh
 norm_num at hh
 have hf:(X:ℝ[X])^3+1=(X+1)*(X^2-X+1):=by ring
 have he:=congrArg (aeval q) hf
 simp only [map_add,map_mul,map_sub,map_pow,map_one,aeval_X] at he
 exact eq_neg_of_add_eq_zero_left (by simpa [show q^2-q+1=0 by rw [hh]; abel] using he)
theorem Oz:seedXQuaternion ^ 2=-1:=by
 rw [LO seedXQuaternion LJ]
 change (((2 * 0:ℝ):ℍ) * seedXQuaternion - 1) = -1
 rw [mul_zero,Quaternion.coe_zero,zero_mul,zero_sub]
open Polynomial in
theorem seedY_fifth:seedYQuaternion ^ 5=-1:=by
 let t:=2*seedGoldenReal
 have ht:t^2-t-1=0:=by dsimp [t]; nlinarith [V6]
 have hc:=congrArg (C:ℝ → ℝ[X]) ht
 simp only [map_sub,map_pow,map_one,map_zero] at hc
 have hf:(X:ℝ[X])^5+1=(X+1)*(X^2-C t*X+1)*(X^2+(C t-1)*X+1):=by
  linear_combination (X+1)*X^2*hc
 let q:=seedYQuaternion
 have hz:q^2-(t:ℍ)*q+1=0:=by rw [LO q LL]; change (t:ℍ)*q-1-_+1=0; abel
 have he:=congrArg (aeval q) hf
 simp only [map_add,map_sub,map_mul,map_pow,map_one,aeval_X,aeval_C] at he
 exact eq_neg_of_add_eq_zero_left (by simpa [show algebraMap ℝ ℍ t * q = (t:ℍ)*q from rfl,hz] using he)
theorem V7:(seedXQuaternion * star seedYQuaternion) ^ 3=-1:=by
 apply vZ
 ·rw [map_mul,Quaternion.normSq_star,LJ,LL,mul_one]
 ·rw [Quaternion.re_mul]
  rw [Quaternion.imI_star]
  norm_num [seedXQuaternion,seedYQuaternion]
theorem OC :
  seedXUnit ^ 2=seedYUnit ^ 5 /\
  seedXUnit ^ 2=(seedXUnit * seedYUnit⁻¹) ^ 3:=by
 constructor
 ·apply Subtype.val_injective
  change seedXQuaternion ^ 2=seedYQuaternion ^ 5
  rw [Oz,seedY_fifth]
 ·apply Subtype.val_injective
  change seedXQuaternion ^ 2=(seedXQuaternion * star seedYQuaternion) ^ 3
  rw [Oz,V7]
def seedRelator:Bool -> FreeGroup Bool
 | false=>FreeGroup.of false ^ 2 * (FreeGroup.of true ^ 5)⁻¹
 | true=>FreeGroup.of false ^ 2 * ((FreeGroup.of false * (FreeGroup.of true)⁻¹) ^ 3)⁻¹
def seedLetterUnit:Bool -> z5
 | false=>seedXUnit
 | true=>seedYUnit
theorem V8 (r:Bool):FreeGroup.lift seedLetterUnit (seedRelator r)=1:=by
 cases r
 ·simp only [seedRelator,map_mul,map_inv,map_pow,FreeGroup.lift_apply_of,seedLetterUnit]
  rw [OC.1,mul_inv_cancel]
 ·simp only [seedRelator,map_mul,map_inv,map_pow,FreeGroup.lift_apply_of,seedLetterUnit]
  rw [OC.2,mul_inv_cancel]
end EilenbergGanea
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea
namespace SeedConnection
def circleWord (e:nF):FreeGroup Bool:=if e.2=0 then FreeGroup.of e.1 else 1
def ab6 (s:jN):FreeGroup Bool:=
 if (jW s).2 then circleWord (dV s) else
  (circleWord (dV s))⁻¹
def boundaryWords (r:Bool):List (FreeGroup Bool):=
 List.ofFn (fun i:Fin (kF r)=>ab6 ⟨r,i⟩)
theorem cn5:∀ r,(boundaryWords r).prod=seedRelator r:=by
 decide
theorem cw6:∀ e:nF,gX e ≠ lW e:=by decide
theorem da2:∀ s:jN,lC s ≠ lC (nI s):=by decide
def circleLabel (e:nF):z5:=FreeGroup.lift seedLetterUnit (circleWord e)
def w0 (s:jN):z5:=
 FreeGroup.lift seedLetterUnit ((boundaryWords s.1).take s.2.val).prod
@[simp] theorem cc8 (r:Bool):(boundaryWords r).length=kF r:=
 List.length_ofFn
@[simp] theorem cq0 (s:jN) :
  (boundaryWords s.1)[s.2.val]'(by simp)=ab6 s:=by
 simp [boundaryWords]
theorem radial_step (s:jN):w0 (nI s)=w0 s *
    (if (jW s).2 then circleLabel (dV s)
      else (circleLabel (dV s))⁻¹):=by
  have hs:s.2.val < (boundaryWords s.1).length:=by simp
  have he:=congrArg (FreeGroup.lift seedLetterUnit) (congrArg List.prod
    (List.take_succ_eq_append_getElem hs))
  rw [List.prod_append,List.prod_singleton,map_mul,cq0] at he
  have hf:FreeGroup.lift seedLetterUnit (ab6 s) =
      if (jW s).2 then circleLabel (dV s)
      else (circleLabel (dV s))⁻¹:=by
    unfold ab6 circleLabel
    split <;> simp
  rw [hf] at he
  change w0 (nI s) =
    FreeGroup.lift seedLetterUnit ((boundaryWords s.1).take s.2.val).prod * _
  rw [<- he]
  unfold w0 nI
  dsimp only
  by_cases hn:s.2.val + 1 < kF s.1
  · rw [Nat.mod_eq_of_lt hn]
  · have hn':s.2.val + 1=kF s.1:=by have hh:=s.2.isLt; omega
    rw [hn',Nat.mod_self,List.take_zero,List.prod_nil,map_one,
      <- cc8,List.take_length,cn5,V8]
def edgeAnchor:SeedEdge -> SeedVertex
 | .inl e=>.inl (gX e)
 | .inr s=>.inr s.1
def edgeLocal:SeedEdge -> SeedVertex -> z5
 | .inl e,v=>if v=.inl (gX e) then 1 else circleLabel e
 | .inr s,v=>if v=.inr s.1 then 1 else w0 s
def faceLocal (s:jN) (v:SeedVertex):z5:=
 if v=.inr s.1 then 1 else
 if v=.inl (lC s) then w0 s else w0 (nI s)
theorem bn4 (s:jN):(nI s).1=s.1:=rfl
theorem faceLocal_incidence (s:jN) (e:SeedEdge) (he:e ∈ lD s)
    (v:SeedVertex) (hv:v ∈ dS e) :
    faceLocal s v=faceLocal s (edgeAnchor e) * edgeLocal e v:=by
  simp only [lD,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl
  · simp only [dS,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [edgeAnchor,edgeLocal]
    · have hd:=cw6 (dV s)
      have hr:=radial_step s
      cases hb:(jW s).2
      · simp only [hb,Bool.false_eq_true,↓reduceIte] at hr
        simp only [lC,hb,Bool.false_eq_true,↓reduceIte,
          edgeAnchor,edgeLocal,faceLocal,Sum.inl_ne_inr,
          Sum.inl.injEq,Ne.symm hd,hd]
        rw [hr]
        group
      · simp only [hb,↓reduceIte] at hr
        simp only [lC,hb,↓reduceIte,edgeAnchor,edgeLocal,faceLocal,
          Sum.inl_ne_inr,Sum.inl.injEq,Ne.symm hd]
        exact hr
  · simp only [dS,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl <;> simp [faceLocal,edgeLocal,edgeAnchor]
  · simp only [dS,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · simp [faceLocal,edgeLocal,edgeAnchor,bn4]
    · simp [faceLocal,edgeLocal,edgeAnchor,bn4,Ne.symm (da2 s)]
def cellRank:SeedCell -> ℕ
 | .inl _=>0
 | .inr (.inl _)=>1
 | .inr (.inr _)=>2
theorem properFace_rank {a b:SeedCell} (h:dD a b):cellRank a < cellRank b:=by
 rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
  simp only [dD,cellRank] at * <;> omega
def upLabel:SeedCell -> SeedCell -> z5
 | .inl v,.inr (.inl e)=>(edgeLocal e v)⁻¹
 | .inl v,.inr (.inr s)=>(faceLocal s v)⁻¹
 | .inr (.inl e),.inr (.inr s)=>(faceLocal s (edgeAnchor e))⁻¹
 | _,_=>1
@[simp] theorem dv4 (a:SeedCell):upLabel a a=1:=by
 rcases a with a | (a | a) <;> rfl
theorem upLabel_trans {a b c:SeedCell} (hab:a=b \/ dD a b)
  (hbc:b=c \/ dD b c):upLabel a b * upLabel b c=upLabel a c:=by
 rcases hab with rfl | hab
 ·simp
 rcases hbc with rfl | hbc
 ·simp
 rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
  rcases c with c | (c | c) <;> simp only [dD] at hab hbc
 simp only [upLabel,<- mul_inv_rev]
 exact congrArg Inv.inv (faceLocal_incidence c b hbc a hab).symm
def g4 (a b:SeedCell):Prop:=a=b \/ seedGraph.Adj a b
theorem z0 {a b:SeedCell}:g4 a b -> g4 b a:=by
 rintro (rfl | h)
 ·exact Or.inl rfl
 ·exact Or.inr h.symm
theorem related_forward {a b:SeedCell} (h:g4 a b) (hr:cellRank a <= cellRank b) :
  a=b \/ dD a b:=by
 rcases h with h | h
 ·exact Or.inl h
 rcases h with h | h
 ·exact Or.inr h
 ·have hd:=properFace_rank h
  omega
def connection (a b:SeedCell):z5 :=upLabel a b * (upLabel b a)⁻¹
@[simp] theorem ds5 (a:SeedCell):connection a a=1:=by simp [connection]
theorem g1 (a b:SeedCell):connection b a=(connection a b)⁻¹:=by simp [connection]
theorem connection_up {a b:SeedCell} (h:a=b ∨ dD a b):connection a b=upLabel a b:=by
 rcases h with rfl | h
 ·simp
 rcases a with a | (a | a) <;> rcases b with b | (b | b) <;>
  simp [dD,connection,upLabel] at *
theorem via_upper {a b m:SeedCell} (h:g4 a b) (ha:a=m ∨ dD a m)
  (hb:b=m ∨ dD b m):connection a b=upLabel a m * (upLabel b m)⁻¹:=by
 rcases le_total (cellRank a) (cellRank b) with r | r
 ·have f:=related_forward h r
  rw [connection_up f,← upLabel_trans f hb]; simp
 ·have f:=related_forward (z0 h) r
  rw [g1 b a,connection_up f,← upLabel_trans f ha]; simp [mul_assoc]
theorem connection_flat {a b c:SeedCell} (hab:g4 a b) (hbc:g4 b c)
  (hac:g4 a c):connection a b * connection b c=connection a c:=by
 obtain ⟨m,hm,H⟩:=Finset.exists_max_image ({a,b,c}:Finset SeedCell) cellRank (by simp)
 have upper {x:SeedCell} (hx:x ∈ ({a,b,c}:Finset SeedCell)):x=m ∨ dD x m:=by
  refine related_forward ?_ (H x hx)
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hm
  rcases hx with rfl|rfl|rfl <;> rcases hm with rfl|rfl|rfl <;>
   first | exact Or.inl rfl | assumption | apply z0; assumption
 have A:=upper (x:=a) (by simp)
 have B:=upper (x:=b) (by simp)
 have C:=upper (x:=c) (by simp)
 rw [via_upper hab A B,via_upper hbc B C,via_upper hac A C]; group
def rankFin (a:SeedCell):Fin 3:=⟨cellRank a,by
 rcases a with a | (a | a) <;> norm_num [cellRank]⟩
theorem adjacent_rank_ne {a b:SeedCell} (h:seedGraph.Adj a b):rankFin a ≠ rankFin b:=by
 intro he
 have he':=congrArg Fin.val he
 change cellRank a=cellRank b at he'
 rcases h with h | h <;> have hh:=properFace_rank h <;> omega
theorem m1 (s:Finset SeedCell) (hs:(s:Set SeedCell).Pairwise seedGraph.Adj) :
  s.card <= 3:=by
 have hi:Set.InjOn rankFin (s:Set SeedCell):=by
  intro a ha b hb he
  by_contra hn
  exact adjacent_rank_ne (hs ha hb hn) he
 have hc:=Finset.card_le_card (Finset.subset_univ (s.image rankFin))
 rwa [Finset.card_image_of_injOn hi,Finset.card_univ,Fintype.card_fin] at hc
def roseLoop:List SeedCell:=
  [.inl (.inl none),.inr (.inl (.inl (false,0))),
    .inl (.inl (some (false,0))),.inr (.inl (.inl (false,1))),
    .inl (.inl (some (false,1))),.inr (.inl (.inl (false,2))),.inl (.inl none)]
theorem roseLoop_edges:roseLoop.IsChain seedGraph.Adj:=by
 simp [roseLoop,List.isChain_cons_cons,seedGraph,dD,dS,gX,lW]
theorem cp8:(List.zipWith connection roseLoop roseLoop.tail).prod=seedXUnit:=by
  simp [roseLoop,connection,cellRank,upLabel,edgeLocal,circleLabel,circleWord,
    gX,seedLetterUnit]
theorem ci5:(List.zipWith connection roseLoop roseLoop.tail).prod ≠ 1:=by
 rw [cp8]
 intro h
 have hh:=congrArg (fun q:z5=>(q:ℍ).re) h
 norm_num [seedXUnit,seedXQuaternion] at hh
end SeedConnection
end EilenbergGanea
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea
namespace LevelTransport
open TraceWords AffineTransport
variable {V:Type*} [Fintype V] [LinearOrder V] (L:SimpleGraph V)
variable (hdim:∀ s:Finset V,(s:Set V).Pairwise L.Adj -> s.card <= 3)
def point (g:a1 L) (hg:0 < b2 L (cE L g)):b0 V:=
 ⟨dW L g,by
  apply oD.mpr
  refine ⟨(gO L (cE L g)).support,
   hdim _ (p9 L _),⟨?_,?_⟩,?_⟩
  ·exact RZ L _
  ·exact Ao L hg
  ·intro v hv
   simp only [Finsupp.notMem_support_iff] at hv
   simp [dW,iJ,hv]⟩
@[simp] theorem LQ (g:a1 L) (hg:0 < b2 L (cE L g)) :
  (point L hdim g hg:V -> ℝ)=dW L g:=rfl
theorem m3 (g:a1 L) (hg:0 < b2 L (cE L g))
  {v:V} (hv:(point L hdim g hg:V -> ℝ) v ≠ 0) :
  v ∈ (gO L (cE L g)).support:=by
 by_contra h
 have he:=Finsupp.notMem_support_iff.mp h
 exact hv (by simp [point,dW,iJ,he])
theorem z7 (g:a1 L) (hg:0 < b2 L (cE L g)) :
  o0 L (point L hdim g hg):=by
 intro a ha v hv
 by_cases hav:a=v
 ·exact Or.inl hav
 ·exact Or.inr (p9 L _
   (m3 L hdim g hg ha) (m3 L hdim g hg hv) hav)
theorem IG (g:a1 L) (x:a8 V)
  (hg:0 < b2 L (cE L g))
  (hgx:0 < b2 L (cE L (g * cQ (a0 L) x)))
  (N:ℕ) (hNg:N <= b2 L (cE L g))
  (hNgx:N <= b2 L (cE L (g * cQ (a0 L) x))) :
  Compatible L (point L hdim g hg) (point L hdim (g * cQ (a0 L) x) hgx) /\
  dist (point L hdim g hg) (point L hdim (g * cQ (a0 L) x) hgx) <=
   2 / (N+1:ℝ):=by
 classical
 obtain ⟨hs,n,_,hn,hbd⟩:=R5 L g x hg hgx
 have hNn:N <= n:=by rcases hn with ⟨he,_⟩ | ⟨he,_⟩ <;> omega
 constructor
 ·intro v w hv hw
  by_cases he:v=w
  ·exact Or.inl he
  ·apply Or.inr
   apply hs _ _ he
   ·rcases hv with hv | hv
    ·exact Finset.mem_union_left _ (m3 L hdim g hg hv)
    ·exact Finset.mem_union_right _ (m3 L hdim _ hgx hv)
   ·rcases hw with hw | hw
    ·exact Finset.mem_union_left _ (m3 L hdim g hg hw)
    ·exact Finset.mem_union_right _ (m3 L hdim _ hgx hw)
 ·have hc:(N:ℝ) + 1 <= (n:ℝ) + 1:=by exact_mod_cast Nat.add_le_add_right hNn 1
  have hd:0 < (N:ℝ) + 1:=by positivity
  have hfrac:2 / (n+1:ℝ) <= 2 / (N+1:ℝ):=
   div_le_div_of_nonneg_left (by norm_num) hd hc
  apply le_trans ?_ hfrac
  change dist (dW L g) (dW L (g * cQ (a0 L) x)) <= _
  apply (dist_pi_le_iff (by positivity)).mpr
  intro v
  rw [Real.dist_eq,abs_sub_comm]
  exact le_trans (Finset.single_le_sum (fun w _=>abs_nonneg (dW L (g * cQ (a0 L) x) w - dW L g w)) (Finset.mem_univ v)) hbd
abbrev a6 (N:ℕ):={g:a1 L // (height L g).toAdd=-(N:ℤ)}
omit [Fintype V] in
theorem y4 (N:ℕ) {g:a1 L}
  (hg:(height L g).toAdd=-(N:ℤ)) :
  N <= b2 L (cE L g):=by
 have hh:=R6 L g
 rw [hg,abs_neg,abs_of_nonneg (Nat.cast_nonneg N)] at hh
 exact_mod_cast hh
def fD (N:ℕ) (hN:0 < N) (g:a6 L N):b0 V:=
 point L hdim g (lt_of_lt_of_le hN (y4 L N g.property))
@[simp] theorem du0 (N:ℕ) (hN:0 < N) (g:a6 L N) :
  (fD L hdim N hN g:V -> ℝ)=dW L g:=rfl
def jI (N:ℕ) (hN:1 < N) (g:a6 L N) (v:V) :
  a6 L (N-1):=
 ⟨(g:a1 L) * a0 L v,by
  rw [map_mul,a4]
  change (height L (g:a1 L)).toAdd + 1=_
  rw [g.property]
  omega⟩
def cD (N:ℕ) (g:a6 L N) (q r:V):a6 L N:=
 ⟨(g:a1 L) * a0 L q * (a0 L r)⁻¹,by
  simp only [map_mul,map_inv,a4]
  change (height L (g:a1 L)).toAdd + 1 + -1=_
  rw [g.property]
  omega⟩
omit [Fintype V] [LinearOrder V] in
theorem tK (N:ℕ) (g:a6 L N) (q r:V) :
  cD L N (cD L N g q r) r q=g:=by
 apply Subtype.ext
 change (g:a1 L) * _ * _ * _ * _=_
 group
omit [Fintype V] [LinearOrder V] in
theorem i6 (N:ℕ) (hN:1 < N) (g:a6 L N) (q r:V) :
  jI L N hN (cD L N g q r) r=jI L N hN g q:=by
 apply Subtype.ext
 dsimp only [cD,jI]
 group
theorem fG (N:ℕ) (hN:1 < N) (g:a6 L N) (v:V) :
  Compatible L (fD L hdim N (by omega) g)
   (fD L hdim (N-1) (by omega) (jI L N hN g v)) /\
  dist (fD L hdim N (by omega) g)
   (fD L hdim (N-1) (by omega) (jI L N hN g v)) <= 2 / (N:ℝ):=by
 let hu:=jI L N hN g v
 have hlen:=y4 L N g.property
 have hlen':=y4 L (N-1) hu.property
 dsimp only [hu,jI] at hlen'
 have H:=IG L hdim (g:a1 L) (v,true)
  (lt_of_lt_of_le (by omega:0 < N) hlen)
  (by simpa only [q2] using lt_of_lt_of_le (by omega:0 < N-1) hlen')
  (N-1) (le_trans (Nat.sub_le N 1) hlen)
  (by simpa only [q2] using hlen')
 have he:((N-1:ℕ):ℝ) + 1=(N:ℝ):=by exact_mod_cast (show (N-1:ℕ) + 1=N by omega)
 simpa only [fD,jI,q2,he] using H
variable (h:V -> V -> a3) (Q:V -> ℍ)
def kC (N:ℕ) (hN:1 < N) (g:a6 L N) (q r:V):a3:=
 fF h Q (fD L hdim N (by omega) g)
  (fD L hdim (N-1) (by omega) (jI L N hN g q))
  (fD L hdim N (by omega) (cD L N g q r))
theorem OD (hf:d7 L h) (hQ:c2 h Q)
  (N:ℕ) (hN:1 < N) (g:a6 L N) (q r:V) :
  kC L hdim h Q N hN (cD L N g q r) r q =
   (kC L hdim h Q N hN g q r)⁻¹:=by
 have h₁:=(fG L hdim N hN g q).1
 have h₂:=(fG L hdim N hN (cD L N g q r) r).1
 rw [i6] at h₂
 unfold kC
 rw [tK,i6]
 exact V0 L h Q hf hQ h₁ (p0 L h₂)
theorem BK (hQ:c2 h Q) {ε:ℝ} (hε:0 < ε) :
  ∃ M:ℕ,∀ N:ℕ,M <= N -> ∀ hN:1 < N,∀ g:a6 L N,∀ q r:V,
   dist (kC L hdim h Q N hN g q r) 1 < ε:=by
 obtain ⟨δ,hδ,H⟩:=V5 h Q hQ hε
 obtain ⟨M,hM⟩:=exists_nat_gt (2 / δ)
 refine ⟨M,?_⟩
 intro N hMN hN g q r
 have hN0:(0:ℝ) < N:=by exact_mod_cast (by omega:0 < N)
 have hbound:2 / (N:ℝ) < δ:=by
  apply (div_lt_iff₀ hN0).mpr
  have hMN':(M:ℝ) <= N:=by exact_mod_cast hMN
  have hh:=(div_lt_iff₀ hδ).mp hM
  nlinarith
 apply H
 ·exact lt_of_le_of_lt (fG L hdim N hN g q).2 hbound
 ·have hh:=(fG L hdim N hN (cD L N g q r) r).2
  rw [i6,dist_comm] at hh
  exact lt_of_le_of_lt hh hbound
omit [LinearOrder V] in
theorem cs1 (hf:d7 L h) (hQ:c2 h Q)
  (b c d u v w:b0 V) (δ:ℝ) (hδ:0 < δ)
  (hsmall:4 * δ < 1 / (Fintype.card V + 1:ℝ))
  (hb:o0 L b) (hc:o0 L c) (hd:o0 L d)
  (hu:o0 L u) (hv:o0 L v) (hw:o0 L w)
  (hbu:Compatible L b u) (huc:Compatible L u c)
  (hcv:Compatible L c v) (hvd:Compatible L v d)
  (hdw:Compatible L d w) (hwb:Compatible L w b)
  (dbu:dist b u <= δ) (duc:dist u c <= δ)
  (dcv:dist c v <= δ) (dvd:dist v d <= δ)
  (_ddw:dist d w <= δ) (dwb:dist w b <= δ) :
  fF h Q b u c * fF h Q c v d * fF h Q d w b=1:=by
 have dbc:dist b c <= 2 * δ:=by linarith [dist_triangle b u c]
 have dbv:dist b v <= 3 * δ:=by linarith [dist_triangle b c v]
 have dbd:dist b d <= 4 * δ:=by linarith [dist_triangle b v d]
 have dbw:dist b w <= δ:=by simpa only [dist_comm] using dwb
 obtain ⟨a,ha⟩:=VT b
 apply wY L h Q hf hQ b c d u v w hbu huc hcv hvd hdw hwb
 ·exact w3 L ha hb (by simpa using lt_of_lt_of_le hδ (le_of_lt (by linarith:δ < 1 / (Fintype.card V + 1:ℝ))))
 ·exact w3 L ha hc (by linarith)
 ·exact w3 L ha hd (lt_of_le_of_lt dbd hsmall)
 ·exact w3 L ha hu (by linarith)
 ·exact w3 L ha hv (by linarith)
 ·exact w3 L ha hw (by linarith)
theorem V9 (hf:d7 L h) (hQ:c2 h Q)
  (N:ℕ) (hN:1 < N) (hsize:8 / (N:ℝ) < 1 / (Fintype.card V + 1:ℝ))
  (g₀ g₁ g₂:a6 L N) (q₀ r₀ q₁ r₁ q₂ r₂:V)
  (e₀:cD L N g₀ q₀ r₀=g₁)
  (e₁:cD L N g₁ q₁ r₁=g₂)
  (e₂:cD L N g₂ q₂ r₂=g₀) :
  kC L hdim h Q N hN g₀ q₀ r₀ *
   kC L hdim h Q N hN g₁ q₁ r₁ *
   kC L hdim h Q N hN g₂ q₂ r₂=1:=by
 have h₀:=fG L hdim N hN g₀ q₀
 have h₁:=fG L hdim N hN g₁ q₁
 have h₂:=fG L hdim N hN g₂ q₂
 have j₀:=fG L hdim N hN g₁ r₀
 have j₁:=fG L hdim N hN g₂ r₁
 have j₂:=fG L hdim N hN g₀ r₂
 rw [<- e₀,i6,e₀] at j₀
 rw [<- e₁,i6,e₁] at j₁
 rw [<- e₂,i6,e₂] at j₂
 unfold kC
 rw [e₀,e₁,e₂]
 apply cs1 L h Q hf hQ _ _ _ _ _ _ (2/(N:ℝ))
 ·positivity
 ·convert hsize using 1; ring
 ·exact z7 L hdim _ _
 ·exact z7 L hdim _ _
 ·exact z7 L hdim _ _
 ·exact z7 L hdim _ _
 ·exact z7 L hdim _ _
 ·exact z7 L hdim _ _
 ·exact h₀.1
 ·exact p0 L j₀.1
 ·exact h₁.1
 ·exact p0 L j₁.1
 ·exact h₂.1
 ·exact p0 L j₂.1
 ·exact h₀.2
 ·simpa only [dist_comm] using j₀.2
 ·exact h₁.2
 ·simpa only [dist_comm] using j₁.2
 ·exact h₂.2
 ·simpa only [dist_comm] using j₂.2
def kL (v:V):b0 V:=
 ⟨fun w=>if v=w then 1 else 0,by
  apply oD.mpr
  refine ⟨{v},by simp,⟨?_,?_⟩,?_⟩
  ·intro w; dsimp only; split_ifs <;> norm_num
  ·simp
  ·intro w hw
   simp only [Finset.mem_singleton] at hw
   simp [Ne.symm hw]⟩
@[simp] theorem OE (v w:V) :
  (kL v:V -> ℝ) w=if v=w then 1 else 0:=rfl
theorem OH {a v:V} (hav:g4 L a v):Star L a (kL v):=by
 intro w hw
 have he:v=w:=by by_contra hh; exact hw (by simp [kL,hh])
 simpa only [<- he] using hav
omit [Fintype V] [LinearOrder V] in
theorem qG {q r:V} (hqr:L.Adj q r) (n m:ℕ) :
  (a0 L q)⁻¹ ^ (n+1) * (a0 L r)⁻¹ ^ m * a0 L q =
   (a0 L q)⁻¹ ^ n * (a0 L r)⁻¹ ^ m:=by
 have hc:=(a2 L hqr).inv_right.pow_right m
 calc
  _=(a0 L q)⁻¹ ^ n *
    ((a0 L q)⁻¹ * ((a0 L r)⁻¹ ^ m * a0 L q)):=by
   simp only [pow_succ]; group
  _=(a0 L q)⁻¹ ^ n *
    ((a0 L q)⁻¹ * (a0 L q * (a0 L r)⁻¹ ^ m)):=by
   rw [<- hc.eq]
  _=_:=by group
theorem bl2 {q r:V} (hqr:L.Adj q r) (n m:ℕ)
  (hg:0 < b2 L (cE L
   ((a0 L q)⁻¹ ^ n * (a0 L r)⁻¹ ^ m))) :
  Star L q (point L hdim ((a0 L q)⁻¹ ^ n * (a0 L r)⁻¹ ^ m) hg):=by
 intro v hv
 by_cases hqv:q=v
 ·exact Or.inl hqv
 by_cases hrv:r=v
 ·exact Or.inr (hrv ▸ hqr)
 exfalso
 apply hv
 rw [LQ,j0 L hqr]
 simp [hqv,hrv]
theorem Wa {q r:V} (hqr:L.Adj q r) (N:ℕ) (hN:0 < N)
  (hg:0 < b2 L (cE L
   ((a0 L q)⁻¹ ^ N * (a0 L r)⁻¹ ^ 0))) :
  point L hdim ((a0 L q)⁻¹ ^ N * (a0 L r)⁻¹ ^ 0) hg =
   kL q:=by
 apply Subtype.ext
 funext v
 rw [LQ,OE,j0 L hqr]
 have hn:(N:ℝ) ≠ 0:=by exact_mod_cast Nat.ne_of_gt hN
 by_cases hv:q=v <;> simp [hv,hn]
theorem Wb {q r:V} (hqr:L.Adj q r) (N:ℕ) (hN:0 < N)
  (hg:0 < b2 L (cE L
   ((a0 L q)⁻¹ ^ 0 * (a0 L r)⁻¹ ^ N))) :
  point L hdim ((a0 L q)⁻¹ ^ 0 * (a0 L r)⁻¹ ^ N) hg =
   kL r:=by
 apply Subtype.ext
 funext v
 rw [LQ,OE,j0 L hqr]
 have hn:(N:ℝ) ≠ 0:=by exact_mod_cast Nat.ne_of_gt hN
 by_cases hv:r=v <;> simp [hv,hn]
def cV (N:ℕ) (q r:V) (j:ℕ):a6 L N:=
 ⟨(a0 L q)⁻¹ ^ (N - min j N) * (a0 L r)⁻¹ ^ min j N,by
  simp only [map_mul,map_pow,map_inv,a4]
  change (N-min j N:ℕ) • (-1:ℤ) + (min j N:ℕ) • (-1:ℤ)=_
  simp only [nsmul_eq_mul,mul_neg,mul_one]
  have hh:min j N <= N:=min_le_right _ _
  omega⟩
omit [Fintype V] [LinearOrder V] in
theorem pZ (N:ℕ) {q r:V} (hqr:L.Adj q r) {j:ℕ} (hj:j < N) :
  cD L N (cV L N q r j) q r=cV L N q r (j+1):=by
 apply Subtype.ext
 dsimp only [cV,cD]
 rw [min_eq_left (by omega:j <= N),min_eq_left (by omega:j+1 <= N)]
 have he:N-j=(N-(j+1))+1:=by omega
 rw [he,qG L hqr,pow_succ]
 group
omit [Fintype V] [LinearOrder V] in
theorem BL (N:ℕ) (hN:1 < N) {q r:V}
  (hqr:L.Adj q r) {j:ℕ} (hj:j < N) :
  (jI L N hN (cV L N q r j) q:a1 L) =
   (a0 L q)⁻¹ ^ (N-(j+1)) * (a0 L r)⁻¹ ^ j:=by
 dsimp only [cV,jI]
 rw [min_eq_left (by omega:j <= N)]
 have he:N-j=(N-(j+1))+1:=by omega
 rw [he,qG L hqr]
theorem OI (N:ℕ) (hN:0 < N) {q r:V} (hqr:L.Adj q r) (j:ℕ) :
  Star L q (fD L hdim N hN (cV L N q r j)):=
 bl2 L hdim hqr _ _ _
theorem wZ (N:ℕ) (hN:1 < N) {q r:V}
  (hqr:L.Adj q r) {j:ℕ} (hj:j < N) :
  Star L q (fD L hdim (N-1) (by omega)
   (jI L N hN (cV L N q r j) q)):=by
 unfold fD
 generalize_proofs hpos
 simp only [BL L N hN hqr hj] at hpos ⊢
 exact bl2 L hdim hqr _ _ _
theorem Cu (hf:d7 L h) (hQ:c2 h Q)
    (N:ℕ) (hN:1 < N) {q r:V} (hqr:L.Adj q r) {j:ℕ} (hj:j < N) :
    kC L hdim h Q N hN (cV L N q r j) q r =
      dY h Q q (fD L hdim N (by omega) (cV L N q r j))
        (fD L hdim N (by omega) (cV L N q r (j+1))):=by
  have hb:=fG L hdim N hN (cV L N q r j) q
  have hc:=fG L hdim N hN (cD L N (cV L N q r j) q r) r
  rw [i6] at hc
  unfold kC
  rw [s8 L h Q hf hQ hb.1 (p0 L hc.1)
    (OI L hdim N (by omega) hqr j) (wZ L hdim N hN hqr hj)]
  · rw [pZ L N hqr hj]
  · rw [pZ L N hqr hj]
    exact OI L hdim N (by omega) hqr (j+1)
def lA (N:ℕ) (q:V):a6 L N:=
 ⟨(a0 L q)⁻¹ ^ N,by
  simp only [map_pow,map_inv,a4]
  change N • (-1:ℤ)=-(N:ℤ)
  simp⟩
omit [Fintype V] [LinearOrder V] in
theorem Wd (N:ℕ) (q r:V) :
  cV L N q r 0=lA L N q:=by apply Subtype.ext; simp [cV,lA]
omit [Fintype V] [LinearOrder V] in
theorem Wf (N:ℕ) (q r:V) :
  cV L N q r N=lA L N r:=by apply Subtype.ext; simp [cV,lA]
def n9 (v:V):a3:=gauge h Q v (kL v)
theorem Wg (N:ℕ) (hN:0 < N) {q r:V} (hqr:L.Adj q r) :
  fD L hdim N hN (cV L N q r 0)=kL q:=by
 unfold fD
 have hh:(cV L N q r 0:a1 L) =
   (a0 L q)⁻¹ ^ N * (a0 L r)⁻¹ ^ 0:=by simp [cV]
 simp only [hh]
 exact Wa L hdim hqr N hN _
theorem Wh (N:ℕ) (hN:0 < N) {q r:V} (hqr:L.Adj q r) :
  fD L hdim N hN (cV L N q r N)=kL r:=by
 unfold fD
 have hh:(cV L N q r N:a1 L) =
   (a0 L q)⁻¹ ^ 0 * (a0 L r)⁻¹ ^ N:=by simp [cV]
 simp only [hh]
 exact Wb L hdim hqr N hN _
omit [Fintype V] [LinearOrder V] in
def gP {a b:V}:L.Walk a b -> a3
 | .nil=>1
 | .cons (u:=u) (v:=v) _ p=>h u v * gP p
omit [Fintype V] [LinearOrder V] in
theorem bd2 {a b:V} (w:L.Walk a b) :
    gP L h w=(List.zipWith h w.support w.support.tail).prod:=by
  induction w with
  | nil=>simp [gP]
  | @cons q t r hqt w ih=>
      cases w with
      | nil=>simp [gP]
      | cons htl p=>simpa only [gP,SimpleGraph.Walk.support_cons,
          List.tail_cons,List.zipWith_cons_cons,List.prod_cons] using congrArg (h q t * ·) ih
end LevelTransport
namespace SourceTransport
open LevelTransport AffineTransport
def seedWalk:seedGraph.Walk (.inl (.inl none)) (.inl (.inl none)):=
 SimpleGraph.Walk.ofSupport SeedConnection.roseLoop
  (by simp [SeedConnection.roseLoop]) SeedConnection.roseLoop_edges
theorem Wi:seedWalk.support=SeedConnection.roseLoop:=
 SimpleGraph.Walk.support_ofSupport _ _
theorem Wj:gP seedGraph SeedConnection.connection seedWalk ≠ 1:=by
 rw [bd2,Wi]
 exact SeedConnection.ci5
end SourceTransport
end EilenbergGanea
end
end OAI
end
/- Based on openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). -/
namespace OAI.EilenbergGanea
noncomputable section
open Classical
variable {V H:Type*} [Group H] (L:SimpleGraph V) (S:Set V)
theorem D8 (a:a1 L → V → H)
  (sq:∀ x ∈ S,∀ y ∈ S,L.Adj x y → ∀ g,
   a g x * a (g * a0 L x) y = a g y * a (g * a0 L y) x) :
  ∃ F:a1 L → H,∀ g x,x ∈ S → F (g * a0 L x) = F g * a g x:=by
 classical
 let B:=((a1 L → H) ⋊[tZ (a1 L) H] a1 L)
 let f:V → B:=fun x=>if x ∈ S then ⟨fun g=>a g x,a0 L x⟩ else 1
 have h (x y) (adj:L.Adj x y):Commute (f x) (f y):=by
  by_cases hx:x ∈ S <;> by_cases hy:y ∈ S <;> simp only [f,hx,hy,if_true,if_false] <;> try first | exact Commute.one_left _ | exact Commute.one_right _
  apply SemidirectProduct.ext
  ·funext g
   exact sq x hx y hy adj g
  ·exact (a2 L adj).eq
 let P:=sW L f h
 let base (g:a1 L):=g * (P g).right⁻¹
 refine ⟨fun g=>(P g).left (base g),?_⟩
 intro g x hx
 have hgen:P (a0 L x) = (⟨fun g=>a g x,a0 L x⟩:B):=by simp [P,f,hx]
 have hb:base (g * a0 L x) = base g:=by
  dsimp only [base]
  rw [map_mul,hgen]
  change g * a0 L x * ((P g).right * a0 L x)⁻¹ = _
  group
 dsimp only
 rw [hb,map_mul,hgen]
 change (P g).left _ * a (base g * (P g).right) x = _
 simp [base,mul_assoc]
end
end OAI.EilenbergGanea
namespace OAI.CubicalChains.VertexDeletion
noncomputable section
open Classical
variable {G A:Type*} [Group G] [LinearOrder A] (L:SimpleGraph A) (v:A → G)
abbrev C (S:Set A) (k:ℕ):Submodule ℤ (Chains G A):=
 Finsupp.supported ℤ ℤ {p | SimplicialChains.Valid L p.2 ∧ p.2.length = k ∧ ∀ a ∈ p.2,a ∈ S}
abbrev Link (S:Set A) (x:A):={a | a ∈ S ∧ x < a ∧ L.Adj x a}
variable {L}
def headIndex (x:A):G × List A ↪ G × List A where
 toFun p:=(p.1,x :: p.2)
 inj':=by rintro ⟨g,w⟩ ⟨h,u⟩ e; simpa using e

def peel (x:A):Chains G A →ₗ[ℤ] Chains G A:=
 Finsupp.lcomapDomain (headIndex x) (headIndex x).injective

theorem IL (x:A) (c:Chains G A):peel x (front x c) = c:=
 Finsupp.ext (Finsupp.mapDomain_apply (headIndex x).injective c)

theorem split {S:Set A} {x:A} (hx:∀ a ∈ S,x ≤ a) {k:ℕ} {c:Chains G A}
  (hc:c ∈ C L S (k+1)):peel x c ∈ C L (Link L S x) k ∧
   c - front x (peel x c) ∈ C L (S \ {x}) (k+1):=by
 let a:=peel x c
 constructor
 ·rintro ⟨g,w⟩ h
  have hn:a (g,w) ≠ 0:=Finsupp.mem_support_iff.mp h
  have ⟨⟨ho,hd⟩,hl,hs⟩:=(Finsupp.mem_supported ℤ c).mp hc (show (g,x::w) ∈ c.support from Finsupp.mem_support_iff.mpr hn)
  obtain ⟨hy,hw⟩:=List.pairwise_cons.mp ho
  obtain ⟨ha,hc⟩:=List.pairwise_cons.mp hd
  exact ⟨⟨hw,hc⟩,by simpa using hl,fun z hz=>⟨hs z (List.mem_cons_of_mem _ hz),hy z hz,ha z hz⟩⟩
 ·rintro p hp
  have h:=Finsupp.mem_support_iff.mp hp
  change c p - Finsupp.mapDomain (headIndex x) a p ≠ 0 at h
  by_cases e:p ∈ Set.range (headIndex x)
  ·obtain ⟨q,rfl⟩:=e
   exact (h (sub_eq_zero.mpr (Finsupp.mapDomain_apply (headIndex x).injective a q).symm)).elim
  rw [Finsupp.mapDomain_of_notMem_range _ _ e,sub_zero] at h
  obtain ⟨⟨ho,hd⟩,hl,hs⟩:=(Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr h)
  refine ⟨⟨ho,hd⟩,hl,fun z hz=>⟨hs z hz,?_⟩⟩
  rcases p with ⟨g,_|⟨y,w⟩⟩
  ·simp at hz
  rcases List.mem_cons.mp hz with rfl | ht
  ·rintro rfl; exact e ⟨(g,w),rfl⟩
  ·exact ne_of_gt (lt_of_le_of_lt (hx y (hs y (by simp))) ((List.pairwise_cons.mp ho).1 z ht))

theorem faces {S:Set A} (g:G) (w:List A) (hs:∀ a ∈ w,a ∈ S) :
  cP v g w ∈ Finsupp.supported ℤ ℤ {p:G × List A | ∀ a ∈ p.2,a ∈ S}:=by
 induction w with
 | nil=>simp
 | cons x w ih=>
  have ht:∀ a ∈ w,a ∈ S:=fun a h=>hs a (List.mem_cons_of_mem _ h)
  rw [dK]
  apply Submodule.sub_mem
  ·apply Submodule.sub_mem <;> exact Finsupp.single_mem_supported ℤ 1 ht
  apply d8 _ _ _ _ (ih ht)
  rintro ⟨g',w'⟩ h
  rw [jO]
  apply Finsupp.single_mem_supported
  intro a ha
  rcases List.mem_cons.mp ha with rfl | h'
  ·exact hs _ (by simp)
  ·exact h _ h'

theorem DQ {x:A} {c:Chains G A}
  (hc:c ∈ Finsupp.supported ℤ ℤ {p:G × List A | ∀ a ∈ p.2,a ≠ x}):peel x c = 0:=by
 ext ⟨g,w⟩
 exact (Finsupp.mem_supported' ℤ c).mp hc (g,x::w) (fun h=>h x (by simp) rfl)

theorem tL {S T:Set A} (h:S ⊆ T) {k} {c:Chains G A} (hc:c ∈ C L S k):c ∈ C L T k:=by
 apply Finsupp.supported_mono _ hc
 rintro p ⟨hv,hl,hs⟩
 exact ⟨hv,hl,fun a ha=>h (hs a ha)⟩

theorem EH {S:Set A} (x:A) {k} {c:Chains G A} (hc:c ∈ C L S k):shift v x c ∈ C L S k:=by
 apply d8 _ _ _ _ hc
 rintro ⟨g,w⟩ h
 rw [Ja]
 exact Finsupp.single_mem_supported ℤ 1 h

theorem Kd {S:Set A} {x:A} (hx:x ∈ S) {k} {c:Chains G A} (hc:c ∈ C L (Link L S x) k):front x c ∈ C L S (k+1):=by
 apply d8 _ _ _ _ hc
 rintro ⟨g,w⟩ ⟨⟨ho,hd⟩,hl,hs⟩
 rw [jO]
 apply Finsupp.single_mem_supported
 refine ⟨⟨List.pairwise_cons.mpr ⟨fun a h=>(hs a h).2.1,ho⟩,List.pairwise_cons.mpr ⟨fun a h=>(hs a h).2.2,hd⟩⟩,by simpa using congrArg Nat.succ hl,?_⟩
 intro a ha
 rcases List.mem_cons.mp ha with rfl | hw
 ·exact hx
 ·exact (hs a hw).1

def Bounds (S:Set A) (k:ℕ):=∀ c ∈ C (G:=G) L S k,boundary v c = 0 → ∃ d ∈ C L S (k+1),boundary v d = c
variable (comm:∀ a b,L.Adj a b → Commute (v a) (v b))
include comm in
theorem IQ {S:Set A} {k} {c:Chains G A} (hc:c ∈ C L S k):boundary v (boundary v c) = 0:=by
 rw [C,Finsupp.supported_eq_span_single] at hc
 induction hc using Submodule.span_induction with
 | mem z hz=>
  obtain ⟨⟨g,w⟩,⟨⟨_,hd⟩,_,_⟩,rfl⟩:=hz
  simpa using qE v g w (hd.imp (fun h=>comm _ _ h))
 | zero=>simp
 | add _ _ _ _ h j=>simp [h,j]
 | smul _ _ _ h=>simp [h]
include comm in
theorem IT {S:Set A} {x:A} (hx:x ∈ S) (hm:∀ a ∈ S,x ≤ a) {k:ℕ}
  (link:Bounds (L:=L) v (Link L S x) k) (del:Bounds (L:=L) v (S \ {x}) (k+1)):Bounds (L:=L) v S (k+1):=by
 intro c hc hz
 let a:=peel x c
 let b:=c - front x a
 have ⟨ha,hb⟩:=split hm hc
 have hab:c = front x a + b:=by dsimp only [b]; abel
 let T:=S \ {x}
 have sub:Link L S x ⊆ T:=fun y hy=>⟨hy.1,ne_of_gt hy.2.1⟩
 have avoids {n} {u:Chains G A} (hu:u ∈ C L T n):peel x u = 0:=by
  apply DQ
  apply Finsupp.supported_mono _ hu
  exact fun p h y hy=>(h.2.2 y hy).2
 have hpb:peel x (boundary v b) = 0:=by
  apply DQ
  apply d8 _ _ _ _ hb
  rintro ⟨g,w⟩ ⟨_,_,hs⟩
  rw [gI,one_smul]
  exact faces v g w (S:={y | y ≠ x}) (fun y hy=>(hs y hy).2)
 have eqn:=congrArg (peel x) hz
 rw [hab,map_add,rF,map_add,map_sub,map_sub,hpb,avoids (tL sub ha),avoids (EH v x (tL sub ha)),IL] at eqn
 obtain ⟨d,hd,he⟩:=link a ha (by simpa using eqn)
 have hp:=Kd hx hd
 let r:=c + boundary v (front x d)
 have hr:r ∈ C L T (k+1):=by
  have re:r = b + shift v x d - d:=by dsimp [r]; rw [hab,rF,he]; abel
  rw [re]
  exact Submodule.sub_mem _ (Submodule.add_mem _ hb (EH v x (tL sub hd))) (tL sub hd)
 obtain ⟨e,he',her⟩:=del r hr (by simp [r,hz,IQ v comm hp])
 refine ⟨e - front x d,Submodule.sub_mem _ (tL (Set.sdiff_subset) he') hp,?_⟩
 rw [map_sub,her]; dsimp [r]; abel

include comm in
theorem EI (base:∀ S:Finset A,Bounds (L:=L) v (S:Set A) 1) (S:Finset A) :
  ∀ k,0 < k → Bounds (L:=L) v (S:Set A) k:=by
 classical
 refine Finset.strongInductionOn (p:=fun U=>∀ k,0 < k → Bounds (L:=L) v (U:Set A) k) S ?_
 intro S ih

 intro k hk
 obtain _ | k:=k
 ·omega
 obtain _ | k:=k
 ·exact base S
 by_cases hn:S.Nonempty
 ·let x:=S.min' hn
  have hx:x ∈ S:=Finset.min'_mem _ _
  let D:=S.erase x
  let T:=S.filter (fun a=>x < a ∧ L.Adj x a)
  have ht:T ⊂ S:=Finset.ssubset_iff_subset_ne.mpr ⟨Finset.filter_subset _ _,fun e=>by
   have h:x ∈ T:=e.symm ▸ hx
   simpa [T] using h⟩
  apply IT v comm (x:=x) hx (fun a ha=>Finset.min'_le _ a ha)
  ·simpa [T,Link,Finset.coe_filter] using ih T ht (k+1) (by omega)
  ·simpa [D,Finset.coe_erase] using ih D (Finset.erase_ssubset hx) (k+1+1) (by omega)
 ·rw [Finset.not_nonempty_iff_eq_empty.mp hn]
  intro c hc _
  have hzero:c = 0:=by
   apply Finsupp.ext
   intro p
   by_contra h
   have ⟨_,hl,hs⟩:=(Finsupp.mem_supported ℤ c).mp hc (Finsupp.mem_support_iff.mpr h)
   rcases p with ⟨g,w⟩
   cases w with
   | nil=>simp at hl
   | cons y w=>simpa using hs y (by simp)
  exact ⟨0,Submodule.zero_mem _,by simp [hzero]⟩
end
end OAI.CubicalChains.VertexDeletion
namespace OAI.EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration CubicalChains.VertexDeletion
variable {V:Type} [LinearOrder V] [Fintype V] (L:SimpleGraph V)
theorem vI
  (base:∀ S:Finset V,Bounds (L:=L) (a0 L) (S:Set V) 1)
  {k:ℕ} (hk:0 < k) (c:Chains (a1 L) V) (hc:c ∈ total L k)
  (hz:boundary (a0 L) c = 0):∃ b ∈ total L (k+1),boundary (a0 L) b = c:=by
 classical
 have e (n:ℕ):C (G:=a1 L) L (↑(Finset.univ:Finset V):Set V) n = total L n:=by
  simp [C,total]
 rw [← e] at hc ⊢
 exact EI (a0 L) (fun _ _=>a2 L) base Finset.univ k hk c hc hz
end OAI.EilenbergGanea.LevelBasis
namespace OAI.EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.VertexDeletion
variable {V:Type} [LinearOrder V] (L:SimpleGraph V)
theorem D9 (S:Set V):Bounds (L:=L) (a0 L) S 1:=by
 classical
 let B:=(C (G:=a1 L) L S 2).map (boundary (a0 L))
 let q:=B.mkQ
 let e (g:a1 L) (x:V):=q (Finsupp.single (g,[x]) 1)
 have square (x y:V) (hx:x ∈ S) (hy:y ∈ S) (h:x < y) (ha:L.Adj x y) (g:a1 L) :
   e g x + e (g * a0 L x) y = e g y + e (g * a0 L y) x:=by
  have hc:Finsupp.single (g,[x,y]) (1:ℤ) ∈ C L S 2:=by
   apply Finsupp.single_mem_supported
   exact ⟨by simp [SimplicialChains.Valid,h,ha],rfl,by simpa using And.intro hx hy⟩
  have hz:q (boundary (a0 L) (Finsupp.single (g,[x,y]) 1)) = 0:=
   (Submodule.Quotient.mk_eq_zero B).mpr ⟨_,hc,rfl⟩
  simp only [gI,one_smul,dK,nJ,map_zero,sub_zero,map_sub,jO] at hz
  dsimp only [e]
  linear_combination (norm:=abel) hz
 obtain ⟨F,hF⟩:=D8 (H:=Multiplicative (_ ⧸ B)) L S (fun g x=>Multiplicative.ofAdd (e g x)) (by
  intro x hx y hy ha g
  rcases lt_or_gt_of_ne (L.ne_of_adj ha) with h | h
  ·exact square x y hx hy h ha g
  ·exact (square y x hy hx h ha.symm g).symm)
 let f:Chains (a1 L) V →ₗ[ℤ] _ ⧸ B:=Finsupp.linearCombination ℤ fun p=>if p.2 = [] then (F p.1).toAdd else 0
 intro c hc hz
 have he:q c = f (boundary (a0 L) c):=by
  clear hz
  rw [C,Finsupp.supported_eq_span_single] at hc
  induction hc using Submodule.span_induction with
  | mem z hz=>
   obtain ⟨⟨g,w⟩,⟨_,hl,hs⟩,rfl⟩:=hz
   obtain ⟨x,rfl⟩:=List.length_eq_one_iff.mp hl
   have h:(F (g * a0 L x)).toAdd = (F g).toAdd + e g x:=hF g x (hs x (by simp))
   simp [f,h,e]
  | zero=>simp
  | add _ _ _ _ h j=>simp [h,j]
  | smul _ _ _ h=>simp [h]
 rw [hz,map_zero] at he
 exact (Submodule.Quotient.mk_eq_zero B).mp he
end OAI.EilenbergGanea.LevelBasis
section
namespace OAI
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A:Type} [Group G] [LinearOrder A]
variable (L:SimpleGraph A) (φ:G →* Multiplicative ℤ) (v:A -> G) (root:A)
def ht (g:G):ℤ:=(φ g).toAdd
@[simp] theorem LW (g q:G):ht φ (g*q)=ht φ g + ht φ q:=by simp [ht]
@[simp] theorem dy2:ht φ 1=0:=by simp [ht]
@[simp] theorem Wk (g:G):ht φ g⁻¹=-ht φ g:=by simp [ht]
@[simp] theorem LX (g:G) (n:ℤ):ht φ (g^n)=n * ht φ g:=by simp [ht]
@[simp] theorem OJ (g:φ.ker):ht φ g=0:=by simp [ht,MonoidHom.mem_ker.mp g.property]
variable (hv:∀ a,φ (v a)=Multiplicative.ofAdd (1:ℤ))
include hv in
omit [LinearOrder A] in
@[simp] theorem y8 (a:A):ht φ (v a)=1:=by simp [ht,hv]
include hv in
omit [LinearOrder A] in
theorem Jv (g:G) (a:A):ht φ (g * v a)=ht φ g + 1:=by simp [y8 φ v hv]
def Shape (k:ℕ):={p:List A × ℤ // SimplicialChains.Valid L p.1 /\ p.1.length=k /\
  p.2 < 0 /\ 0 < p.2 + (k:ℤ)}
def jA (k:ℕ) (p:φ.ker × Shape L k):G × List A:=
 (p.1.val * (v (p.2.val.1.headD root)) ^ p.2.val.2,p.2.val.1)
include hv in
theorem al2 (k:ℕ) (p:φ.ker × Shape L k) :
  ht φ (jA L φ v root k p).1=p.2.val.2:=by
 simp only [jA,LW,OJ,LX,y8 φ v hv,mul_one,zero_add]
include hv in
theorem OL (k:ℕ):Function.Injective (jA L φ v root k):=by
 intro p q he
 have hw:p.2.val.1=q.2.val.1:=congrArg Prod.snd he
 have hh:=congrArg (fun x=>ht φ x.1) he
 rw [al2 L φ v root hv,al2 L φ v root hv] at hh
 have hs:p.2=q.2:=Subtype.ext (Prod.ext hw hh)
 have hg:=congrArg Prod.fst he
 simp only [jA,hs] at hg
 exact Prod.ext (Subtype.ext (mul_right_cancel hg)) hs
include hv in
theorem Wm (k:ℕ) (p:φ.ker × Shape L k) :
  SimplicialChains.Valid L (jA L φ v root k p).2 /\
   (jA L φ v root k p).2.length=k /\
   ht φ (jA L φ v root k p).1 < 0 /\
   0 < ht φ (jA L φ v root k p).1 + (k:ℤ):=by
 rw [al2 L φ v root hv]
 exact p.2.property
include hv in
theorem Wn {k:ℕ} (p:G × List A)
  (hp:SimplicialChains.Valid L p.2 /\ p.2.length=k /\ ht φ p.1 < 0 /\ 0 < ht φ p.1 + (k:ℤ)) :
  ∃ q:φ.ker × Shape L k,jA L φ v root k q=p:=by
 let s:Shape L k:=⟨(p.2,ht φ p.1),hp⟩
 let g:φ.ker:=⟨p.1 * (v (p.2.headD root)) ^ (-ht φ p.1),by
  apply (Multiplicative.toAdd.injective)
  change ht φ (p.1 * (v (p.2.headD root)) ^ (-ht φ p.1))=0
  simp only [LW,LX,y8 φ v hv,mul_one,add_neg_cancel]⟩
 refine ⟨(g,s),?_⟩
 apply Prod.ext
 ·change (p.1 * (v (p.2.headD root)) ^ (-ht φ p.1)) * (v (p.2.headD root)) ^ (ht φ p.1)=p.1
  rw [mul_assoc,<- zpow_add,neg_add_cancel,zpow_zero,mul_one]
 ·rfl
def gJ (k:ℕ):(φ.ker × Shape L k →₀ ℤ) →ₗ[ℤ] CubicalChains.Chains G A:=
 Finsupp.lmapDomain ℤ ℤ (jA L φ v root k)
@[simp] theorem t4 (k:ℕ) (p:φ.ker × Shape L k) (n:ℤ) :
  gJ L φ v root k (Finsupp.single p n)=Finsupp.single (jA L φ v root k p) n:=by
 simp [gJ]
include hv in
theorem k0 (k:ℕ):Function.Injective (gJ L φ v root k):=
 Finsupp.mapDomain_injective (OL L φ v root hv k)
include hv in
theorem LY (k:ℕ):LinearMap.range (gJ L φ v root k)=crossing L (ht φ) k:=by
 rw [gJ,Finsupp.range_lmapDomain,crossing,Finsupp.supported_eq_span_single]
 congr 1
 ext c
 constructor
 ·rintro ⟨p,rfl⟩
  exact ⟨jA L φ v root k p,Wm L φ v root hv k p,rfl⟩
 ·rintro ⟨p,hp,rfl⟩
  obtain ⟨q,rfl⟩:=Wn L φ v root hv p hp
  exact ⟨q,rfl⟩
variable (comm:∀ a b,L.Adj a b -> Commute (v a) (v b))
include hv in
def LZ (k:ℕ):CubicalChains.Chains G A →ₗ[ℤ] (φ.ker × Shape L k →₀ ℤ):=
 Finsupp.lcomapDomain (jA L φ v root k) (OL L φ v root hv k)
@[simp] theorem Wq (k:ℕ) (c:φ.ker × Shape L k →₀ ℤ) :
  LZ L φ v root hv k (gJ L φ v root k c)=c:=
 Finsupp.leftInverse_lcomapDomain_mapDomain _ _ c
include hv in
theorem Wr {k:ℕ} {c:CubicalChains.Chains G A} (hc:c ∈ crossing L (ht φ) k) :
  gJ L φ v root k (LZ L φ v root hv k c)=c:=by
 rw [<- LY L φ v root hv k] at hc
 obtain ⟨d,rfl⟩:=hc
 rw [Wq]
include hv in
theorem L6 (k:ℕ) (c:φ.ker × Shape L k →₀ ℤ) :
  gJ L φ v root k c ∈ crossing L (ht φ) k:=by
 rw [<- LY L φ v root hv k]
 exact ⟨c,rfl⟩
def generator (s:Shape L 2):φ.ker:=
 ⟨(v (s.val.1.headD root))⁻¹ * v (s.val.1.tail.headD root),by simp [hv]⟩
def oF:(φ.ker →₀ ℤ) →ₗ[ℤ] CubicalChains.Chains G A:=
 Finsupp.lmapDomain ℤ ℤ (fun g=>(g.val,[]))
omit [LinearOrder A] in
@[simp] theorem Ws (g:φ.ker) (n:ℤ) :
  oF (A:=A) φ (Finsupp.single g n)=Finsupp.single (g.val,[]) n:=by simp [oF]
include hv in
omit [LinearOrder A] in
theorem CZ (g:G) (a b:A) (hab:Commute (v a) (v b))
    (hg:ht φ g=-1) :
    f8 v (ht φ) (Finsupp.single (g,[a,b]) 1) =
      Finsupp.single (g*v b,[]) 1 - Finsupp.single (g*v a,[]) 1:=by
  have hga:ht φ (g * v a)=0:=by rw [Jv φ v hv,hg]; omega
  have hgb:ht φ (g * v b)=0:=by rw [Jv φ v hv,hg]; omega
  simp only [s5,gI,one_smul,dK,nJ,
    map_zero,sub_zero,map_sub,jO,plus,N4,hga,hgb,hg]
  norm_num
  rw [mul_assoc,hab.eq,<- mul_assoc]
  abel
include hv comm in
theorem rO (p:φ.ker × Shape L 2) :
    f8 v (ht φ) (gJ L φ v root 2 (Finsupp.single p 1)) =
      oF (A:=A) φ (bY (generator L φ v root hv) (Finsupp.single p 1)):=by
  rcases p with ⟨g,⟨⟨w,n⟩,hs⟩⟩
  obtain ⟨a,b,hw⟩:=List.length_eq_two.mp hs.2.1
  change w=[a,b] at hw
  subst w
  have hn:n=-1:=by have h₁:=hs.2.2.1; have h₂:=hs.2.2.2; norm_num at h₂; omega
  subst n
  have hab:L.Adj a b:=(List.pairwise_cons.mp hs.1.2).1 b (by simp)
  rw [t4]
  change f8 v (ht φ) (Finsupp.single (g.val * (v a)^(-1:ℤ),[a,b]) 1)=_
  rw [CZ φ v hv _ a b (comm a b hab) (by simp [y8 φ v hv])]
  simp only [bY,Finsupp.linearCombination_single]
  simp only [zpow_neg_one,one_smul,map_sub,Ws,
    Subgroup.coe_mul,generator,List.headD_cons,List.tail_cons,mul_assoc,inv_mul_cancel,mul_one]
include hv comm in
theorem Wt (c:φ.ker × Shape L 2 →₀ ℤ) :
  f8 v (ht φ) (gJ L φ v root 2 c) =
   oF (A:=A) φ (bY (generator L φ v root hv) c):=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simp only [map_add,hc,hd]
 | single p n=>
  have he:Finsupp.single p n=n • Finsupp.single p (1:ℤ):=by simp
  rw [he,map_smul,map_smul,map_smul,map_smul,rO L φ v root hv comm]
def fO:(φ.ker × Shape L 3 →₀ ℤ) →ₗ[ℤ] (φ.ker × Shape L 2 →₀ ℤ):=
 (LZ L φ v root hv 2).comp ((iQ (ht φ)).comp ((boundary v).comp (gJ L φ v root 3)))
include hv in
theorem e7 (c:φ.ker × Shape L 3 →₀ ℤ) :
  gJ L φ v root 2 (fO L φ v root hv c) =
   iQ (ht φ) (boundary v (gJ L φ v root 3 c)):=by
 apply Wr L φ v root hv
 exact Lh L (ht φ) (Lj L v (ht φ) (Jv φ v hv)
  (Kw L (ht φ) (L6 L φ v root hv 3 c)))
variable (K:SimplicialChains.Contraction L)
variable (exactTotal:∀ {k:ℕ},0 < k -> ∀ c,c ∈ total (G:=G) L k -> boundary v c=0 ->
   ∃ b ∈ total (G:=G) L (k+1),boundary v b=c)
variable (dim:∀ w,SimplicialChains.Valid L w -> w.length <= 3)
include hv comm K exactTotal dim in
theorem OO:Function.Injective (fO L φ v root hv):=by
 suffices hz:∀ c,fO L φ v root hv c=0 -> c=0 by
  intro c d he
  exact sub_eq_zero.mp (hz (c-d) (by simp only [map_sub,he,sub_self]))
 intro c hc
 apply k0 L φ v root hv 3
 rw [map_zero]
 apply SK L v (ht φ) K (Jv φ v hv) comm exactTotal dim
  _ (L6 L φ v root hv 3 c)
 rw [<- e7 L φ v root hv,hc,map_zero]
end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
variable {V:Type} [LinearOrder V] (L:SimpleGraph V)
def tM (a b:V) (hab:a < b) (hadj:L.Adj a b):Shape L 2:=
 ⟨([a,b],-1),by simp [SimplicialChains.Valid,hab,hadj]⟩
@[simp] theorem OP (root a b:V) (hab:a < b) (hadj:L.Adj a b) :
  (generator L (height L) (a0 L) root (a4 L)
   (tM L a b hab hadj)).val=(a0 L a)⁻¹ * a0 L b:=rfl
theorem OQ (hconn:L.Preconnected) (root:V) :
  Function.Surjective (FreeGroup.lift (generator L (height L) (a0 L) root (a4 L))):=by
 let f:=FreeGroup.lift (generator L (height L) (a0 L) root (a4 L))
 let F:=(height L).ker.subtype.comp f
 have hgen:c6 L <= F.range:=by
  apply (Subgroup.closure_le _).mpr
  rintro x ⟨a,b,hadj,rfl⟩
  have hab:a ≠ b:=L.ne_of_adj hadj
  rcases lt_or_gt_of_ne hab with hab | hab
  ·refine ⟨(FreeGroup.of (tM L a b hab hadj))⁻¹,?_⟩
   change (f ((FreeGroup.of (tM L a b hab hadj))⁻¹)).val=_
   simp only [f,map_inv,FreeGroup.lift_apply_of,Subgroup.coe_inv,OP,mul_inv_rev,inv_inv]
   exact (a2 L hadj).inv_right.eq.symm
  ·refine ⟨FreeGroup.of (tM L b a hab hadj.symm),?_⟩
   change (f (FreeGroup.of (tM L b a hab hadj.symm))).val=_
   simp only [f,FreeGroup.lift_apply_of,OP]
   exact (a2 L hadj).inv_right.eq.symm
 intro g
 have he:g.val ∈ c6 L:=by rw [qJ L hconn root]; exact g.property
 obtain ⟨w,hw⟩:=hgen he
 exact ⟨w,Subtype.ext hw⟩
end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration
variable {V:Type} [LinearOrder V] [Fintype V] [Nonempty V] (L:SimpleGraph V)
theorem j5 {k:ℕ} (hk:0 < k)
  (c:Chains (a1 L) V) (hc:c ∈ total (G:=a1 L) L k)
  (hz:boundary (a0 L) c=0) :
  ∃ b ∈ total (G:=a1 L) L (k+1),boundary (a0 L) b=c:=by
 exact vI L (fun S=>D9 L S) hk c hc hz
end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.LevelExact CubicalChains.HeightFiltration
variable {G A:Type} [Group G] [LinearOrder A]
variable (L:SimpleGraph A) (φ:G →* Multiplicative ℤ) (v:A -> G) (root:A)
variable (hv:∀ a,φ (v a)=Multiplicative.ofAdd (1:ℤ))
variable (comm:∀ a b,L.Adj a b -> Commute (v a) (v b))
instance L7 [Fintype A] (k:ℕ):Finite (Shape L k):=by
 let f:Shape L k -> List.Vector A k × Fin k:=fun s=>
  (⟨s.val.1,s.property.2.1⟩,⟨(-s.val.2).toNat,by
   have hn:=s.property.2.2.1
   have hm:=s.property.2.2.2
   omega⟩)
 apply Finite.of_injective f
 intro s t h
 apply Subtype.ext
 apply Prod.ext
 ·exact congrArg (fun p:List.Vector A k × Fin k=>p.1.val) h
 ·have he:=congrArg (fun p:List.Vector A k × Fin k=>p.2.val) h
  have hs:=s.property.2.2.1
  have ht:=t.property.2.2.1
  dsimp [f] at he
  omega
noncomputable instance du1 [Fintype A] (k:ℕ):Fintype (Shape L k):=Fintype.ofFinite _
def dM (a b:A) (hab:SimplicialChains.Valid L [a,b]):Shape L 2:=
 ⟨([a,b],-1),hab,rfl,by norm_num,by norm_num⟩
def pN (a b c:A) (habc:SimplicialChains.Valid L [a,b,c])
  (n:ℤ) (hn:n=-1 \/ n=-2):Shape L 3:=
 ⟨([a,b,c],n),habc,rfl,by omega,by norm_num; omega⟩
@[simp] theorem n3 (a b:A) (hab:SimplicialChains.Valid L [a,b]) :
  (generator L φ v root hv (dM L a b hab):G)=(v a)⁻¹ * v b:=rfl
theorem b5 {a b c:A} (h:SimplicialChains.Valid L [a,b,c]) :
  SimplicialChains.Valid L [a,b] /\ SimplicialChains.Valid L [a,c] /\
   SimplicialChains.Valid L [b,c]:=by
 simp [SimplicialChains.Valid] at h ⊢
 tauto
include comm in
theorem rD (a b c:A) (h:SimplicialChains.Valid L [a,b,c]) :
    ((v a)⁻¹ * v b) * ((v b)⁻¹ * v c)=(v a)⁻¹ * v c /\
    ((v b)⁻¹ * v c) * ((v a)⁻¹ * v b)=(v a)⁻¹ * v c:=by
  have he:=b5 L h
  have ha:L.Adj a b:=by simpa [SimplicialChains.Valid] using he.1.2
  have hb:L.Adj a c:=by simpa [SimplicialChains.Valid] using he.2.1.2
  have hc:L.Adj b c:=by simpa [SimplicialChains.Valid] using he.2.2.2
  constructor
  · group
  · calc
      ((v b)⁻¹ * v c) * ((v a)⁻¹ * v b)=(v a)⁻¹ * ((v b)⁻¹ * v c) * v b:=by
        rw [<- mul_assoc,
          ((comm a b ha).inv_left.inv_right.mul_right (comm a c hb).inv_left).symm.eq]
      _=(v a)⁻¹ * v c:=by
        rw [mul_assoc,mul_assoc,<- (comm b c hc).eq,inv_mul_cancel_left]
def jL (ab ac bc:Shape L 2):FreeGroup (Shape L 2):=
 FreeGroup.of ac * (FreeGroup.of bc)⁻¹ * (FreeGroup.of ab)⁻¹
def iW (ab ac bc:Shape L 2):FreeGroup (Shape L 2):=
 FreeGroup.of ab * (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹) *
  (FreeGroup.of ab)⁻¹
include comm in
theorem mK (a b c:A) (h:SimplicialChains.Valid L [a,b,c]) :
    let e:=b5 L h
    let ab:=dM L a b e.1
    let ac:=dM L a c e.2.1
    let bc:=dM L b c e.2.2
    aD (generator L φ v root hv) (jL L ab ac bc)=1 /\
      aD (generator L φ v root hv) (iW L ab ac bc)=1:=by
  dsimp only
  have he:=rD L v comm a b c h
  constructor <;> apply Subtype.ext
  · simp only [jL,map_mul,map_inv,aD,FreeGroup.lift_apply_of,
      Subgroup.coe_mul,Subgroup.coe_inv,n3,OneMemClass.coe_one]
    group
  · simp only [iW,map_mul,map_inv,aD,FreeGroup.lift_apply_of,
      Subgroup.coe_mul,Subgroup.coe_inv,n3,OneMemClass.coe_one]
    rw [he.2,mul_inv_cancel,mul_one,mul_inv_cancel]
/-- The two successive sides of a lifted triangle, minus its diagonal. -/
def Bv (w:Shape L 2 -> G) (g:G) (p q d:Shape L 2):(G × Shape L 2) →₀ ℤ:=
 Finsupp.single (g,p) 1 + Finsupp.single (g * w p,q) 1 - Finsupp.single (g,d) 1

theorem Fz (w:Shape L 2 -> G) (ab ac bc:Shape L 2)
  (u:w ab * w bc=w ac) (t:w bc * w ab=w ac) (g:G) (low:Prop) [Decidable low] :
  aW w (if low then jL L ab ac bc else iW L ab ac bc) g =
   if low then -Bv L w g ab bc ac else Bv L w (g*w ab) bc ab ac:=by
 by_cases h:low <;> simp only [h,if_true,if_false,Bv]
 ·simp only [jL,d2,f9,Lq,map_mul,map_inv,aD,FreeGroup.lift_apply_of]
  rw [← u]
  simp only [mul_assoc,mul_inv_cancel,mul_one]
  abel
 ·have hr:aD w (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹)=1:=by
   simp only [aD,map_mul,map_inv,FreeGroup.lift_apply_of,t,mul_inv_cancel]
  rw [iW,n5 w _ _ hr]
  simp only [d2,f9,Lq,map_mul,aD,FreeGroup.lift_apply_of]
  rw [t]
  simp only [mul_assoc,u,mul_inv_cancel,mul_one]
  abel
def p8:(w:List A) -> SimplicialChains.Valid L w -> ℤ -> FreeGroup (Shape L 2)
 | [a,b,c],h,n=>
  let e:=b5 L h
  if n=-1 then
   jL L (dM L a b e.1) (dM L a c e.2.1) (dM L b c e.2.2)
  else iW L (dM L a b e.1) (dM L a c e.2.1) (dM L b c e.2.2)
 | _,_,_=>1
def kQ (s:Shape L 3):FreeGroup (Shape L 2):=
 p8 L s.val.1 s.property.1 s.val.2
theorem qA (s:Shape L 3) :
  ∃ (a b c:A) (h:SimplicialChains.Valid L [a,b,c]) (n:ℤ) (hn:n=-1 \/ n=-2),
   s=pN L a b c h n hn:=by
 obtain ⟨a,b,c,hw⟩:=List.length_eq_three.mp s.property.2.1
 have hn:s.val.2=-1 \/ s.val.2=-2:=by
  have h₁:=s.property.2.2.1
  have h₂:=s.property.2.2.2
  norm_num at h₂
  omega
 refine ⟨a,b,c,hw ▸ s.property.1,s.val.2,hn,?_⟩
 exact Subtype.ext (Prod.ext hw rfl)
include comm in
theorem OT (s:Shape L 3) :
  aD (generator L φ v root hv) (kQ L s)=1:=by
 obtain ⟨a,b,c,h,n,hn,rfl⟩:=qA L s
 rcases hn with rfl | rfl
 ·simpa [kQ,p8,pN] using
   (mK L φ v root hv comm a b c h).1
 ·simpa [kQ,p8,pN] using
   (mK L φ v root hv comm a b c h).2
include comm in
theorem Wv (s:Shape L 3) (g:φ.ker) :
    aW (generator L φ v root hv) (kQ L s) g =
      fO L φ v root hv (Finsupp.single (g,s) 1):=by
  obtain ⟨a,b,c,h,n,hn,rfl⟩:=qA L s
  let e:=b5 L h
  let ab:=dM L a b e.1
  let ac:=dM L a c e.2.1
  let bc:=dM L b c e.2.2
  let w:=generator L φ v root hv
  have he:=rD L v comm a b c h
  have u:w ab * w bc=w ac:=Subtype.ext he.1
  have t:w bc * w ab=w ac:=Subtype.ext he.2
  change aW w (if n=-1 then jL L ab ac bc else iW L ab ac bc) g = _
  rw [Fz L w ab ac bc u t]
  have slide (x:A) (hx:L.Adj a x):(v a)^(-2:ℤ) * v x=(v a)⁻¹ * (v x * (v a)⁻¹):=by
    rw [← (comm a x hx).inv_left.eq]; group
  have hb:=slide b (by simpa [SimplicialChains.Valid] using e.1.2)
  have hc:=slide c (by simpa [SimplicialChains.Valid] using e.2.1.2)
  have ha:(v a)^(-2:ℤ) * v a=(v a)⁻¹:=by group
  simp only [zpow_neg,zpow_ofNat] at ha hb hc
  symm
  rcases hn with rfl | rfl <;> simp only [if_true,show (-2:ℤ) ≠ -1 by decide,if_false] <;>
    simp only [Bv,mul_assoc,u] <;> apply k0 L φ v root hv 2 <;> rw [e7 L φ v root hv] <;>
    simp only [w,ab,ac,bc,map_neg,map_sub,map_add,t4,jA,pN,dM,
      List.headD_cons,Subgroup.coe_mul,generator,List.tail_cons,gI,one_smul,
      dK,nJ,map_zero,sub_zero,jO,iQ,N4,
      Finsupp.linearCombination_single,LW,OJ,Wk,LX,y8 φ v hv,List.length_cons,List.length_nil] <;>
    norm_num <;> simp only [mul_assoc,ha,hb,hc,mul_inv_cancel,mul_one] <;> abel
end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open CubicalChains CubicalChains.HeightFiltration
variable {G A:Type} [Group G] [LinearOrder A]
variable (L:SimpleGraph A) (φ:G →* Multiplicative ℤ) (v:A -> G) (root:A)
variable (hv:∀ a,φ (v a)=Multiplicative.ofAdd (1:ℤ))
variable (comm:∀ a b,L.Adj a b -> Commute (v a) (v b))
include comm in
theorem L9 :
    fO L φ v root hv =
      aO (generator L φ v root hv) (kQ L):=by
  apply Finsupp.lhom_ext'
  intro p
  apply LinearMap.ext
  intro n
  simp only [LinearMap.coe_comp,Function.comp_apply,Finsupp.lsingle_apply,
    aO,Finsupp.linearCombination_single]
  have he:Finsupp.single p n=n • Finsupp.single p (1:ℤ):=by simp
  rw [he,map_smul,<- Wv L φ v root hv comm p.2 p.1]
variable (K:SimplicialChains.Contraction L)
variable (exactTotal:∀ {k:ℕ},0 < k -> ∀ c,c ∈ total (G:=G) L k -> boundary v c=0 ->
   ∃ b ∈ total (G:=G) L (k+1),boundary v b=c)
variable (dim:∀ w,SimplicialChains.Valid L w -> w.length <= 3)
open CubicalChains.LevelExact
include hv comm in
theorem OV (c:φ.ker × Shape L 3 →₀ ℤ) :
  fO L φ v root hv c ∈ cycles (generator L φ v root hv):=by
 rw [L9 L φ v root hv comm]
 exact (zU _ _ (OT L φ v root hv comm) c).property
include hv comm K exactTotal in
theorem O1:LinearMap.range (fO L φ v root hv) =
  cycles (generator L φ v root hv):=by
 apply le_antisymm
 ·rintro _ ⟨c,rfl⟩
  exact OV L φ v root hv comm c
 ·intro c hc
  have hz:f8 v (ht φ) (gJ L φ v root 2 c)=0:=by
   rw [Wt L φ v root hv comm,LinearMap.mem_ker.mp hc,map_zero]
  obtain ⟨t,ht,hdt⟩:=SI L v (ht φ) K (Jv φ v hv) comm exactTotal
   _ (L6 L φ v root hv 2 c) hz
  rw [<- LY L φ v root hv 3] at ht
  obtain ⟨b,rfl⟩:=ht
  refine ⟨b,k0 L φ v root hv 2 ?_⟩
  rwa [e7 L φ v root hv]
noncomputable def zV:(φ.ker × Shape L 3 →₀ ℤ) ≃ₗ[ℤ]
  cycles (generator L φ v root hv):=
 LinearEquiv.ofBijective
  ((fO L φ v root hv).codRestrict (cycles (generator L φ v root hv))
   (OV L φ v root hv comm))
  ⟨fun c d h=>OO L φ v root hv comm K exactTotal dim
   (congrArg Subtype.val h),fun c=>by
    have hc:c.val ∈ LinearMap.range (fO L φ v root hv):=by
     rw [O1 L φ v root hv comm K exactTotal]
     exact c.property
    obtain ⟨b,hb⟩:=hc
    exact ⟨b,Subtype.ext hb⟩⟩
theorem Ww (c:φ.ker × Shape L 3 →₀ ℤ) :
  (zV L φ v root hv comm K exactTotal dim c:φ.ker × Shape L 2 →₀ ℤ) =
   aO (generator L φ v root hv) (kQ L) c:=by
 change fO L φ v root hv c=_
 rw [L9 L φ v root hv comm]
end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
variable {V:Type} [LinearOrder V] [Fintype V] [Nonempty V] (L:SimpleGraph V)
theorem q7 (root:V) (hconn:L.Preconnected)
  (K:SimplicialChains.Contraction L)
  (dim:∀ w,SimplicialChains.Valid L w -> w.length <= 3) :
  cohomologicalDimension (height L).ker <= 2:=by
 exact w4
  (generator L (height L) (a0 L) root (a4 L))
  (OQ L hconn root)
  (fO L (height L) (a0 L) root (a4 L))
  (by rw [L9 _ _ _ _ _ (fun _ _ h=>a2 L h)]; exact o7 _ _)
  (OO L (height L) (a0 L) root (a4 L)
   (fun _ _ h=>a2 L h) K (j5 L) dim)
  (O1 L (height L) (a0 L) root (a4 L)
   (fun _ _ h=>a2 L h) K (j5 L))
end EilenbergGanea.LevelBasis
namespace EilenbergGanea.LevelBasis
open LevelTransport
variable {V:Type} [LinearOrder V] (L:SimpleGraph V) (root:V) (N:ℕ)
noncomputable def eD:(height L).ker ≃ a6 L N where
 toFun:=fun g=>⟨(a0 L root)⁻¹ ^ N * g.val,by
  simp only [map_mul,map_pow,map_inv,a4]
  rw [show height L g.val=1 from g.property,mul_one]
  change N • (-1:ℤ)=-(N:ℤ)
  simp⟩
 invFun:=fun g=>⟨a0 L root ^ N * g.val,by
  change (height L (a0 L root ^ N * g.val)).toAdd=0
  simp only [map_mul,map_pow,a4]
  change N • (1:ℤ) + (height L g.val).toAdd=0
  rw [g.property]
  simp⟩
 left_inv:=fun g=>Subtype.ext (by dsimp; group)
 right_inv:=fun g=>Subtype.ext (by dsimp; group)
def kM (a:a6 L N -> V -> V -> a3)
  (g:(height L).ker) (s:Shape L 2):a3:=
 a (eD L root N g) (s.val.1.tail.headD root) (s.val.1.headD root)
@[simp] theorem Wz (a:a6 L N -> V -> V -> a3)
  (g:(height L).ker) (q r:V) (h:SimplicialChains.Valid L [q,r]) :
  kM L root N a g (dM L q r h)=a (eD L root N g) r q:=rfl
theorem WA (g:(height L).ker) (q r:V)
  (h:SimplicialChains.Valid L [q,r]) :
  eD L root N
    (g * generator L (height L) (a0 L) root (a4 L) (dM L q r h)) =
   cD L N (eD L root N g) r q:=by
 have ha:L.Adj q r:=by simpa [SimplicialChains.Valid] using h.2
 apply Subtype.ext
 simp only [eD,Equiv.coe_fn_mk,Subgroup.coe_mul,n3,cD]
 rw [mul_assoc,(a2 L ha).inv_left.eq]
 group
theorem s4 (g:(height L).ker) (q r:V)
  (h:SimplicialChains.Valid L [q,r]) :
  eD L root N
    (g * (generator L (height L) (a0 L) root (a4 L) (dM L q r h))⁻¹) =
   cD L N (eD L root N g) q r:=by
 have he:=WA L root N
  (g * (generator L (height L) (a0 L) root (a4 L) (dM L q r h))⁻¹)
  q r h
 simp only [inv_mul_cancel_right] at he
 simpa only [tK] using congrArg (fun x=>cD L N x q r) he.symm
variable (a:a6 L N -> V -> V -> a3)
variable (rev:∀ g q r,a (cD L N g q r) r q=(a g q r)⁻¹)
include rev in
theorem WB (g:(height L).ker) (q r:V)
  (h:SimplicialChains.Valid L [q,r]) :
  (kM L root N a
   (g * (generator L (height L) (a0 L) root (a4 L) (dM L q r h))⁻¹)
   (dM L q r h))⁻¹=a (eD L root N g) q r:=by
 rw [Wz,s4,rev,inv_inv]
def jF (q r:V) (h:L.Adj q r):FreeGroup (Shape L 2):=
 if hlt:q < r then
  (FreeGroup.of (dM L q r (by simpa [SimplicialChains.Valid] using And.intro hlt h)))⁻¹
 else
  FreeGroup.of (dM L r q (by
   have hlt':r < q:=lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm (L.ne_of_adj h))
   simpa [SimplicialChains.Valid] using And.intro hlt' h.symm))
theorem WC (q r:V) (h:L.Adj q r) :
    (aD (generator L (height L) (a0 L) root (a4 L))
      (jF L q r h):a1 L) =
        a0 L q * (a0 L r)⁻¹:=by
  unfold jF
  split_ifs
  · simp only [map_inv,aD,FreeGroup.lift_apply_of,Subgroup.coe_inv,n3,
      mul_inv_rev,inv_inv]
    exact (a2 L h).inv_right.symm.eq
  · simp only [aD,FreeGroup.lift_apply_of,n3]
    exact (a2 L h).inv_right.symm.eq
theorem KG (g:(height L).ker) (q r:V) (h:L.Adj q r) :
  eD L root N
   (g * aD (generator L (height L) (a0 L) root (a4 L))
    (jF L q r h))=cD L N (eD L root N g) q r:=by
 apply Subtype.ext
 simp only [eD,Equiv.coe_fn_mk,Subgroup.coe_mul,WC,cD,mul_assoc]
include rev in
theorem O2 (g:(height L).ker) (q r:V) (h:L.Adj q r) :
  aR (generator L (height L) (a0 L) root (a4 L))
   (kM L root N a) (jF L q r h) g=a (eD L root N g) q r:=by
 unfold jF
 split_ifs
 ·simp only [e5,f2,aD,FreeGroup.lift_apply_of]
  exact WB L root N a rev g q r _
 ·exact f2 _ _ _ _
variable (tri:∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
  cD L N g₀ q₀ r₀=g₁ -> cD L N g₁ q₁ r₁=g₂ ->
   cD L N g₂ q₂ r₂=g₀ -> a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂=1)
section
include rev tri in
private theorem Cc {i j k l m n:V} (x:L.Adj i j) (y:L.Adj k l) (z:L.Adj m n)
  (hr:aD (generator L (height L) (a0 L) root (a4 L)) ((jF L) i j x * (jF L) k l y * (jF L) m n z)=1) (g:(height L).ker) :
  aR (generator L (height L) (a0 L) root (a4 L)) (kM L root N a) ((jF L) i j x * (jF L) k l y * (jF L) m n z) g=1:=by
 simp only [d4,O2 L root N a rev,map_mul,← mul_assoc]
 apply tri
 ·exact (KG L root N _ _ _ x).symm
 ·exact (KG L root N _ _ _ y).symm
 ·rw [← KG L root N _ _ _ z]
  simp only [map_mul] at hr
  rw [mul_assoc,mul_assoc,← mul_assoc (aD (generator L (height L) (a0 L) root (a4 L)) _),hr,mul_one]
include rev tri in
theorem WE (s:Shape L 3) (g:(height L).ker) :
  aR (generator L (height L) (a0 L) root (a4 L)) (kM L root N a) (kQ L s) g=1:=by
 obtain ⟨q,r,t,h,n,hn,rfl⟩:=qA L s
 have E:=b5 L h
 have side {i j:V} (v:SimplicialChains.Valid L [i,j]) :
   ∃ e:L.Adj i j,(jF L) i j e=(FreeGroup.of (dM L i j v))⁻¹ ∧
    (jF L) j i e.symm=FreeGroup.of (dM L i j v):=by
  have hlt:i<j:=by simpa using v.1
  exact ⟨by simpa using v.2,by simp [jF,hlt],by simp [jF,not_lt_of_gt hlt]⟩
 obtain ⟨x,x₁,x₂⟩:=side E.1
 obtain ⟨y,y₁,y₂⟩:=side E.2.1
 obtain ⟨z,z₁,z₂⟩:=side E.2.2
 have H:=mK L (height L) (a0 L) root (a4 L) (fun _ _ hh=>a2 L hh) q r t h
 let ab:=dM L q r E.1
 let ac:=dM L q t E.2.1
 let bc:=dM L r t E.2.2
 rcases hn with rfl | rfl
 ·change aR (generator L (height L) (a0 L) root (a4 L)) _ (FreeGroup.of ac * (FreeGroup.of bc)⁻¹ * (FreeGroup.of ab)⁻¹) g=1
  simpa only [y₂,z₁,x₁] using Cc L root N a rev tri y.symm z x
   (by simpa only [jL,y₂,z₁,x₁] using H.1) g
 ·change aR (generator L (height L) (a0 L) root (a4 L)) _ (iW L ab ac bc) g=1
  have hr:aD (generator L (height L) (a0 L) root (a4 L)) (FreeGroup.of bc * FreeGroup.of ab * (FreeGroup.of ac)⁻¹)=1:=by
   have hh:=H.2
   change aD (generator L (height L) (a0 L) root (a4 L)) (FreeGroup.of ab * _ * (FreeGroup.of ab)⁻¹)=1 at hh
   rwa [map_mul,map_inv,mul_inv_eq_one,map_mul,mul_eq_left] at hh
  rw [iW,p7 _ _ _ _ hr]
  have T:=Cc L root N a rev tri z.symm x.symm y (by simpa only [z₂,x₂,y₁] using hr)
  simp only [z₂,x₂,y₁] at T
  rw [T,mul_one,mul_inv_cancel]
end
section
open AffineTransport
variable [Fintype V] (hdim:∀ s:Finset V,(s:Set V).Pairwise L.Adj -> s.card <= 3)
variable (h:V -> V -> a3) (Q:V -> ℍ) (hf:d7 L h) (hQ:c2 h Q) (hN:1 < N)
include hf hQ in
private theorem Jw {q r:V} (e:L.Adj q r) (x:(height L).ker)
    (hx:eD L root N x=lA L N q) (k:ℕ) (hk:k ≤ N) :
    eD L root N (x * aD (generator L (height L) (a0 L) root (a4 L)) (jF L q r e ^ k))=cV L N q r k ∧
    (aR (generator L (height L) (a0 L) root (a4 L)) (kM L root N (kC L hdim h Q N hN))) (jF L q r e ^ k) x=dY h Q q (kL q)
      (fD L hdim N (by omega) (cV L N q r k)):=by
  induction k with
  | zero=>rw [Wg L hdim N (by omega) e,Wd]; simp [hx,dY]
  | succ k ih=>
    obtain ⟨he,hp⟩:=ih (by omega)
    rw [pow_succ,map_mul (aD (generator L (height L) (a0 L) root (a4 L))),← mul_assoc,KG,he,d4,hp,
      O2 L root N (kC L hdim h Q N hN) (OD L hdim h Q hf hQ N hN),he,
      Cu L hdim h Q hf hQ N hN e (by omega),qU]
    exact ⟨pZ L N e (by omega),rfl⟩
include hf hQ in
private theorem Jx {q r:V} (p:L.Walk q r) (x:(height L).ker)
  (hx:eD L root N x=lA L N q) :
  ∃ w,eD L root N (x * aD (generator L (height L) (a0 L) root (a4 L)) w)=lA L N r ∧
   (aR (generator L (height L) (a0 L) root (a4 L)) (kM L root N (kC L hdim h Q N hN))) w x=(n9 h Q q)⁻¹ * gP L h p * n9 h Q r:=by
 induction p generalizing x with
 | nil=>exact ⟨1,by simpa using hx,by simp [gP]⟩
 | @cons q t r e p ih=>
  obtain ⟨he,hp⟩:=Jw L root N hdim h Q hf hQ hN e x hx N le_rfl
  rw [Wf] at he
  obtain ⟨w,hw,hl⟩:=ih _ he
  refine ⟨jF L q t e ^ N * w,by rwa [map_mul (aD (generator L (height L) (a0 L) root (a4 L))),← mul_assoc],?_⟩
  rw [d4,hp,hl,Wh L hdim N (by omega) e]
  simp only [gP]
  unfold dY n9
  rw [LI L h Q hf hQ (Or.inr e) (OH L (Or.inr e)) (OH L (Or.inl rfl))]
  group
include hf hQ in
private theorem WH {q:V} (p:L.Walk q q) (hp:gP L h p ≠ 1) :
  ∃ w x,aD (generator L (height L) (a0 L) root (a4 L)) w=1 ∧ (aR (generator L (height L) (a0 L) root (a4 L)) (kM L root N (kC L hdim h Q N hN))) w x ≠ 1:=by
 let x:=(eD L root N).symm (lA L N q)
 have hx:eD L root N x=lA L N q:=(eD L root N).apply_symm_apply _
 obtain ⟨w,he,hl⟩:=Jx L root N hdim h Q hf hQ hN p x hx
 refine ⟨w,x,mul_left_cancel (((eD L root N).injective (he.trans hx.symm)).trans (mul_one x).symm),?_⟩
 intro eq
 apply hp
 calc
  _ = n9 h Q q * (aR (generator L (height L) (a0 L) root (a4 L)) (kM L root N (kC L hdim h Q N hN))) w x * (n9 h Q q)⁻¹:=by rw [hl]; group
  _ = 1:=by rw [eq]; group
end
end EilenbergGanea.LevelBasis
namespace EilenbergGanea.SourceTransport
open AffineTransport LevelTransport LevelBasis
theorem source_small_labels [LinearOrder SeedCell] (root:SeedCell) (ε:ℝ) (hε:0 < ε) :
  ∃ N:ℕ,1 < N /\ ∃ a:a6 seedGraph N -> SeedCell -> SeedCell -> a3,
   (∀ g q r,a (cD seedGraph N g q r) r q=(a g q r)⁻¹) /\
   (∀ g q r,dist (a g q r) 1 < ε) /\
   (∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
    cD seedGraph N g₀ q₀ r₀=g₁ ->
    cD seedGraph N g₁ q₁ r₁=g₂ ->
    cD seedGraph N g₂ q₂ r₂=g₀ ->
    a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂=1) /\
   ∃ w x,aD (generator seedGraph (height seedGraph) (a0 seedGraph) root (a4 seedGraph)) w=1 ∧
    aR (generator seedGraph (height seedGraph) (a0 seedGraph) root (a4 seedGraph))
     (kM seedGraph root N a) w x ≠ 1:=by
 obtain ⟨Q,hQ⟩:=VE SeedConnection.connection
 have hf:d7 seedGraph SeedConnection.connection:=
  fun _ _ _ hab hbc hac=>SeedConnection.connection_flat hab hbc hac
 obtain ⟨M,hM⟩:=BK seedGraph SeedConnection.m1
  SeedConnection.connection Q hQ hε
 let D:=Fintype.card SeedCell + 1
 let N:=max M (8 * D + 2)
 have hMN:M <= N:=le_max_left _ _
 have hNbound:8 * D + 2 <= N:=le_max_right _ _
 have hN:1 < N:=by omega
 have hD:(0:ℝ) < D:=by dsimp [D]; positivity
 have hNr:(0:ℝ) < N:=by exact_mod_cast (by omega:0 < N)
 have hsize:8 / (N:ℝ) < 1 / (Fintype.card SeedCell + 1:ℝ):=by
  have hBN:(8:ℝ) * D + 2 <= N:=by exact_mod_cast hNbound
  have hDcast:(D:ℝ)=(Fintype.card SeedCell:ℝ) + 1:=by simp [D]
  rw [<- hDcast]
  apply (div_lt_div_iff₀ hNr hD).mpr
  nlinarith
 let a:=kC seedGraph SeedConnection.m1
  SeedConnection.connection Q N hN
 refine ⟨N,hN,a,?_,?_,?_,?_⟩
 ·exact OD seedGraph SeedConnection.m1
   SeedConnection.connection Q hf hQ N hN
 ·exact hM N hMN hN
 ·exact V9 seedGraph SeedConnection.m1
   SeedConnection.connection Q hf hQ N hN hsize
 ·exact WH seedGraph root N SeedConnection.m1 SeedConnection.connection Q hf hQ hN seedWalk Wj
end EilenbergGanea.SourceTransport
namespace EilenbergGanea.LevelBasis
open LevelTransport
variable {V:Type} [LinearOrder V] [Fintype V] [Nonempty V] (L:SimpleGraph V)
variable [Group.ResiduallyFinite (height L).ker]
variable (root:V) (hconn:L.Preconnected)
variable (K:SimplicialChains.Contraction L)
variable (dim:∀ w,SimplicialChains.Valid L w -> w.length <= 3)
include root hconn K dim in
theorem qV
    (small:∀ ε:ℝ,0 < ε ->
      ∃ N:ℕ,1 < N /\ ∃ a:a6 L N -> V -> V -> a3,
      (∀ g q r,a (cD L N g q r) r q=(a g q r)⁻¹) /\
      (∀ g q r,dist (a g q r) 1 < ε) /\
      (∀ g₀ g₁ g₂ q₀ r₀ q₁ r₁ q₂ r₂,
        cD L N g₀ q₀ r₀=g₁ ->
        cD L N g₁ q₁ r₁=g₂ ->
        cD L N g₂ q₂ r₂=g₀ ->
        a g₀ q₀ r₀ * a g₁ q₁ r₁ * a g₂ q₂ r₂=1) /\
       ∃ w x,aD (generator L (height L) (a0 L) root (a4 L)) w=1 ∧
         aR (generator L (height L) (a0 L) root (a4 L)) (kM L root N a) w x ≠ 1)
    {A R:Type*} (a₀:A -> (height L).ker)
    (ha₀:Function.Surjective (aD a₀))
    (r₀:R -> FreeGroup A) (hr₀:∀ i,aD a₀ (r₀ i)=1)
    (hp₀:(aD a₀).ker=Subgroup.normalClosure (Set.range r₀))
    (E:aE (height L).ker R ≃ₗ[ℤ] cycles a₀)
    (hE:∀ c,(E c:aE (height L).ker A)=aO a₀ r₀ c):False:=by
  let gen:=generator L (height L) (a0 L) root (a4 L)
  let comm:=fun q r h=>@a2 V L q r h
  let B:=zV L (height L) (a0 L) root (a4 L)
    comm K (j5 L) dim
  obtain ⟨η,hη,hηa⟩:=Vc gen
    (OQ L hconn root) (kQ L)
    (OT L (height L) (a0 L) root (a4 L) comm)
    B (Ww L (height L) (a0 L) root (a4 L)
      comm K (j5 L) dim) a₀ ha₀ r₀ hr₀ hp₀ E hE
  obtain ⟨N,_,a,ha,hb,ht,w,x,hw,hx⟩:=small η hη
  apply hx
  exact hηa (kM L root N a)
    (fun x s=>by
      simpa only [kM,Subtype.dist_eq,dist_eq_norm,OneMemClass.coe_one] using
        hb (eD L root N x) (s.val.1.tail.headD root) (s.val.1.headD root))
    (WE L root N a ha ht) w hw x
end EilenbergGanea.LevelBasis
end
noncomputable section
open Classical Set
namespace EilenbergGanea
section CliqueSquare
variable {V:Type*} (L:SimpleGraph V)
 def mL (v:V):a1 L →* Multiplicative ℤ:=by
  classical
  exact sW L (fun w=>Multiplicative.ofAdd (if w=v then 1 else 0))
    (fun _ _ _=>Commute.all _ _)
@[simp] theorem ar2 [DecidableEq V] (v w:V) :
    mL L v (a0 L w)=Multiplicative.ofAdd (if w=v then 1 else 0):=by
  classical
  simp [mL]
 def lO (v b:V):(height L).ker:=
  ⟨a0 L v * (a0 L b)⁻¹,by simp⟩
 theorem WI (v w b:V)
    (hvw:L.Adj v w) (hvb:L.Adj v b) (hwb:L.Adj w b) :
    Commute (lO L v b) (lO L w b):=by
  apply Subtype.ext
  exact (((a2 L hvw).mul_right
    (a2 L hvb).inv_right).mul_left
      (((a2 L hwb).symm.inv_left).mul_right (Commute.refl _)))
end CliqueSquare
 def seedCliqueVertex:SeedCell:=.inl (.inl none)
 def seedCliqueEdge:SeedCell:=.inr (.inl (.inl (false,0)))
 def seedCliqueFace:SeedCell:=.inr (.inr ⟨false,⟨0,by decide⟩⟩)
section CupCocycle
open groupCohomology
variable {G:Type} [Group G]
def r8 (a b:G →* Multiplicative ℤ):cocycles₂ (Rep.trivial ℤ G ℤ):=
 ⟨fun p=>(a p.1).toAdd * (b p.2).toAdd,by
  rw [mem_cocycles₂_iff]
  intro g h j
  simp only [map_mul,toAdd_mul]
  change ((a g).toAdd + (a h).toAdd) * (b j).toAdd + (a g).toAdd * (b h).toAdd =
   (a h).toAdd * (b j).toAdd + (a g).toAdd * ((b h).toAdd + (b j).toAdd)
  ring⟩
theorem WJ (a b:G →* Multiplicative ℤ) (g h:G)
  (hc:Commute g h)
  (hag:(a g).toAdd=1) (hah:(a h).toAdd=0)
  (hbg:(b g).toAdd=0) (hbh:(b h).toAdd=1) :
  ⇑(r8 a b) ∉ coboundaries₂ (Rep.trivial ℤ G ℤ):=by
 rintro ⟨f,hf⟩
 have h₁:=congrFun hf (g,h)
 have h₂:=congrFun hf (h,g)
 change f h - f (g*h) + f g=(a g).toAdd * (b h).toAdd at h₁
 change f g - f (h*g) + f h=(a h).toAdd * (b g).toAdd at h₂
 rw [hag,hbh] at h₁
 rw [hah,hbg,<- hc.eq] at h₂
 change (f h:ℤ) - f (g*h) + f g=1 * 1 at h₁
 change (f g:ℤ) - f (g*h) + f h=0 * 0 at h₂
 linarith
theorem WK (a b:G →* Multiplicative ℤ) (g h:G)
  (hc:Commute g h)
  (hag:(a g).toAdd=1) (hah:(a h).toAdd=0)
  (hbg:(b g).toAdd=0) (hbh:(b h).toAdd=1) :
  H2π _ (r8 a b) ≠ 0:=by
 intro he
 exact WJ a b g h hc hag hah hbg hbh
  ((H2π_eq_zero_iff (A:=Rep.trivial ℤ G ℤ) (r8 a b)).mp he)
end CupCocycle
section CliqueCohomology
open groupCohomology
variable {V:Type} (L:SimpleGraph V)
theorem WL (v w b:V)
  (hvw:L.Adj v w) (hvb:L.Adj v b) (hwb:L.Adj w b) :
  ∃ x:H2 (Rep.trivial ℤ (height L).ker ℤ),x ≠ 0:=by
 classical
 let a:=(mL L v).comp (height L).ker.subtype
 let d:=(mL L w).comp (height L).ker.subtype
 have hvw':=L.ne_of_adj hvw
 have hvb':=L.ne_of_adj hvb
 have hwb':=L.ne_of_adj hwb
 refine ⟨H2π _ (r8 a d),WK a d
  (lO L v b) (lO L w b)
  (WI L v w b hvw hvb hwb) ?_ ?_ ?_ ?_⟩
 all_goals simp [a,d,lO,hvw',hvw'.symm,hvb'.symm,hwb'.symm]
end CliqueCohomology
open CategoryTheory CategoryTheory.Limits
theorem x5 (G:Type) [Group G]
    (hx:∃ x:groupCohomology.H2 (Rep.trivial ℤ G ℤ),x ≠ 0) :
    2 <= cohomologicalDimension G:=by
  let A:=Rep.trivial ℤ G ℤ
  let F:=Rep.toModuleMonoidAlgebra (k:=ℤ) (G:=G)
  let:F.Additive:=Functor.additive_of_preserves_binary_products F
  change (2:ℕ) <= projectiveDimension (F.obj A)
  rw [projectiveDimension_ge_iff]
  intro hd
  let:=HasExt.standard (Rep ℤ G)
  let:=HasExt.standard (ModuleCat (MonoidAlgebra ℤ G))
  have:HasProjectiveDimensionLT A 2:=by
    apply HasProjectiveDimensionLT.mk
    intro n hn Y e
    apply (F.mapExt_bijective_of_preservesProjectiveObjects A Y n).injective
    rw [map_zero]
    exact Abelian.Ext.eq_zero_of_hasProjectiveDimensionLT _ 2 hn
  let P:=ProjectiveResolution.of A
  have hz:IsZero (groupCohomology A 2):=by
    apply IsZero.of_iso _ (groupCohomologyIsoExt A 2 ≪≫ @ProjectiveResolution.isoExt ℤ _ _ _ _ Rep.instLinear _ _ P 2 A)
    rw [← HomologicalComplex.exactAt_iff_isZero_homology,
      HomologicalComplex.exactAt_iff' _ 1 2 3 (by simp) (by simp),ShortComplex.moduleCat_exact_iff]
    intro f hf
    exact (P.extMk_eq_zero_iff f 3 rfl hf 1 rfl).1
      ((P.extMk f 3 rfl hf).eq_zero_of_hasProjectiveDimensionLT 2 le_rfl)
  obtain ⟨x,hx⟩:=hx
  exact hx ((ModuleCat.isZero_iff_subsingleton.mp hz).elim x 0)
theorem x6 {V:Type} (L:SimpleGraph V)
  (v w b:V) (hvw:L.Adj v w) (hvb:L.Adj v b) (hwb:L.Adj w b) :
  2 <= cohomologicalDimension (height L).ker:=
 x5 _ (WL L v w b hvw hvb hwb)
theorem source_two_le_cohomologicalDimension:2 <= cohomologicalDimension SourceGroup:=by
 apply x6 seedGraph seedCliqueVertex seedCliqueEdge seedCliqueFace
 ·change dD _ _ \/ _
  left
  simp [dD,seedCliqueVertex,seedCliqueEdge,dS,gX]
 ·change dD _ _ \/ _
  left
  simp [dD,seedCliqueVertex,seedCliqueFace,xP,lD,dS,dV,jW,seedWord,gX,lW]
 ·change dD _ _ \/ _
  left
  simp [dD,seedCliqueEdge,seedCliqueFace,lD,dV,jW,seedWord]
end EilenbergGanea
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea.SeedEncoding
@[simp] theorem cellEquiv_symm_apply (i:Fin 103):cellEquiv.symm i=cellAt i:=rfl
end EilenbergGanea.SeedEncoding
namespace EilenbergGanea
noncomputable abbrev sourceVertexOrder:LinearOrder SeedCell:=
 LinearOrder.lift' SeedEncoding.cellEquiv SeedEncoding.cellEquiv.injective
local instance:LinearOrder SeedCell:=sourceVertexOrder
local instance:Preorder SeedCell:=sourceVertexOrder.toPartialOrder.toPreorder
local instance:LT SeedCell:=sourceVertexOrder.toLT
local instance:LE SeedCell:=sourceVertexOrder.toLE
@[simp] theorem sourceVertexOrder_lt (a b:SeedCell) :
  a < b ↔ SeedEncoding.cellEquiv a < SeedEncoding.cellEquiv b:=Iff.rfl
theorem source_valid_to_index (w:List SeedCell) (hw:SimplicialChains.Valid seedGraph w) :
    SimplicialChains.Valid SeedChainCertificate.graph (w.map SeedEncoding.cellEquiv):=by
  constructor
  · rw [List.pairwise_map]
    exact hw.1
  · rw [List.pairwise_map]
    simpa only [SeedChainCertificate.graph,SimpleGraph.comap_adj,
      <- SeedEncoding.cellEquiv_symm_apply,Equiv.symm_apply_apply] using hw.2
theorem index_valid_to_source (w:List (Fin 103))
  (hw:SimplicialChains.Valid SeedChainCertificate.graph w) :
  SimplicialChains.Valid seedGraph (w.map SeedEncoding.cellEquiv.symm):=by
 constructor
 ·rw [List.pairwise_map]
  simpa only [sourceVertexOrder_lt,Equiv.apply_symm_apply] using hw.1
 ·rw [List.pairwise_map]
  exact hw.2
noncomputable def sourceLinkContraction (K:SimplicialChains.Contraction SeedChainCertificate.graph) :
  SimplicialChains.Contraction seedGraph:=
 K.reindex SeedEncoding.cellEquiv.symm (index_valid_to_source) (source_valid_to_index)
end EilenbergGanea
namespace EilenbergGanea
local instance:LinearOrder SeedCell:=sourceVertexOrder
local instance:Preorder SeedCell:=sourceVertexOrder.toPartialOrder.toPreorder
local instance:LT SeedCell:=sourceVertexOrder.toLT
local instance:LE SeedCell:=sourceVertexOrder.toLE
theorem source_valid_length_le (w:List SeedCell) (hw:SimplicialChains.Valid seedGraph w) :
  w.length <= 3:=by
 simpa only [List.length_map] using
  SeedChainCertificate.valid_length_le (w.map SeedEncoding.cellEquiv) (source_valid_to_index w hw)
theorem source_cd_eq_two_of_contraction
  (K:SimplicialChains.Contraction SeedChainCertificate.graph) :
  cohomologicalDimension SourceGroup=2:=by
 apply le_antisymm
 ·exact LevelBasis.q7 seedGraph seedBase seed_connected.preconnected
   (sourceLinkContraction K) source_valid_length_le
 ·exact source_two_le_cohomologicalDimension
theorem source_no_boundary_basis_of_contraction
  (K:SimplicialChains.Contraction SeedChainCertificate.graph)
  {A R:Type*} (a₀:A -> SourceGroup)
  (ha₀:Function.Surjective (aD a₀))
  (r₀:R -> FreeGroup A) (hr₀:∀ i,aD a₀ (r₀ i)=1)
  (hp₀:(aD a₀).ker=Subgroup.normalClosure (Set.range r₀))
  (E:aE SourceGroup R ≃ₗ[ℤ] cycles a₀)
  (hE:∀ c,(E c:aE SourceGroup A)=aO a₀ r₀ c):False:=by
 let:Group.ResiduallyFinite SourceGroup:=source_residuallyFinite
 exact LevelBasis.qV seedGraph seedBase seed_connected.preconnected
  (sourceLinkContraction K) source_valid_length_le (SourceTransport.source_small_labels seedBase)
  a₀ ha₀ r₀ hr₀ hp₀ E hE
end EilenbergGanea
end
noncomputable section
open Classical Set Metric Topology
open Set Metric Topology
namespace EilenbergGanea.CWCover
abbrev e8 (n:ℕ):=closedBall (0:Fin n -> ℝ) 1
def jB (n:ℕ):e8 n:=⟨0,by simp⟩
instance dr5 (n:ℕ):ContractibleSpace (e8 n):=
 contractibleSpace_closedBall (by norm_num)
instance dg4 (n:ℕ):LocallyPathConnectedSpace (e8 n):=
 (convex_closedBall (0:Fin n -> ℝ) 1).locallyPathConnectedSpace
variable {X E:Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ:Set X)] {p:E -> X} (cov:IsCoveringMap p)
abbrev Cell (n:ℕ):=Topology.RelCWComplex.cell (univ:Set X) n
def characteristic {n:ℕ} (i:Cell (X:=X) n):C(e8 n,X):=
 ⟨fun z=>Topology.RelCWComplex.map n i z.val,
  continuousOn_iff_continuous_domRestrict.mp (Topology.RelCWComplex.continuousOn n i)⟩
abbrev b3 (n:ℕ):=Σ i:Cell (X:=X) n,{e:E // p e=characteristic i (jB n)}
noncomputable def i7 {n:ℕ} (c:b3 (p:=p) n):C(e8 n,E):=
 (cov.existsUnique_continuousMap_lifts (characteristic c.1) (jB n) c.2.val c.2.property).exists.choose
@[simp] theorem u6 {n:ℕ} (c:b3 (p:=p) n) :
  i7 cov c (jB n)=c.2.val:=
 (cov.existsUnique_continuousMap_lifts (characteristic c.1) (jB n) c.2.val c.2.property).exists.choose_spec.1
theorem b9 {n:ℕ} (c:b3 (p:=p) n) (z:e8 n) :
  p (i7 cov c z)=characteristic c.1 z:=
 congrFun (cov.existsUnique_continuousMap_lifts (characteristic c.1) (jB n) c.2.val c.2.property).exists.choose_spec.2 z
theorem WM {n:ℕ} {c d:b3 (p:=p) n}
  (hi:c.1=d.1) (z:e8 n) (hz:i7 cov c z=i7 cov d z):c=d:=by
 have he:(i7 cov c:e8 n -> E)=i7 cov d:=
  cov.eq_of_comp_eq (i7 cov c).continuous (i7 cov d).continuous
   (by ext t; simp only [Function.comp_apply,b9,hi]) z hz
 have hc:c.2.val=d.2.val:=by
  simpa only [u6] using congrFun he (jB n)
 rcases c with ⟨i,e,he⟩
 rcases d with ⟨j,f,hf⟩
 dsimp at hi hc
 cases hi
 cases hc
 rfl
end EilenbergGanea.CWCover
namespace EilenbergGanea.CWCover
open Classical
variable {X E:Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ:Set X)] [T2Space X]
variable {p:E -> X} (cov:IsCoveringMap p)
omit [T2Space X] in
theorem u0 {n:ℕ} (i:Cell (X:=X) n) (z:e8 n)
  (e:E) (he:p e=characteristic i z) :
  ∃ c:b3 (p:=p) n,c.1=i /\ i7 cov c z=e:=by
 obtain ⟨f,hfz,hfp⟩:=(cov.existsUnique_continuousMap_lifts (characteristic i) z e he).exists
 let c:b3 (p:=p) n:=⟨i,f (jB n),congrFun hfp (jB n)⟩
 refine ⟨c,rfl,?_⟩
 have hf:(i7 cov c:e8 n -> E)=f:=
  cov.eq_of_comp_eq (i7 cov c).continuous f.continuous
   (by ext w; rw [Function.comp_apply,b9 cov c w]; exact (congrFun hfp w).symm)
   (jB n) (u6 cov c)
 rw [hf]
 exact hfz
end EilenbergGanea.CWCover
end
noncomputable section
open Classical Set Topology
open Classical Set
namespace EilenbergGanea.CubicalSingular
variable {X Y Z:Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
abbrev I:=unitInterval
abbrev a5 (X:Type*) [TopologicalSpace X]:=C(I,X)
abbrev c4 (X:Type*) [TopologicalSpace X]:=C(I × I,X)
abbrev i2 (X:Type*) [TopologicalSpace X]:=C(I × I × I,X)
abbrev C₀ (X:Type*):=X →₀ ℤ
abbrev C₁ (X:Type*) [TopologicalSpace X]:=a5 X →₀ ℤ
abbrev C₂ (X:Type*) [TopologicalSpace X]:=c4 X →₀ ℤ
abbrev C₃ (X:Type*) [TopologicalSpace X]:=i2 X →₀ ℤ
section
variable {A B D:Type*} [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace D]
abbrev Chains (A X:Type*) [TopologicalSpace A] [TopologicalSpace X]:=C(A,X) →₀ ℤ
def post (f:C(X,Y)):Chains A X →ₗ[ℤ] Chains A Y:=
 Finsupp.lmapDomain ℤ ℤ (fun σ=>f.comp σ)
@[simp] theorem nY (f:C(X,Y)) (σ:C(A,X)) (z:ℤ) :
  post f (Finsupp.single σ z) = Finsupp.single (f.comp σ) z:=by simp [post]
theorem post_comp (g:C(Y,Z)) (f:C(X,Y)) :
  post (A:=A) (g.comp f) = (post g).comp (post f):=by ext; simp
/-- Extend a universal chain by postcomposition with each singular cube. -/
def realize (u:Chains B A):Chains A X →ₗ[ℤ] Chains B X:=
 Finsupp.linearCombination ℤ (fun σ=>post σ u)
theorem pI (u:Chains B A) (f:C(X,Y)) :
  (realize u).comp (post f) = (post f).comp (realize u):=by
 apply Finsupp.lhom_ext
 intro σ z
 simp [realize,post_comp]
theorem realize_comp (v:Chains D B) (u:Chains B A) :
  (realize (X:=X) v).comp (realize u) = realize (realize v u):=by
 apply Finsupp.lhom_ext
 intro σ z
 simpa [realize,Finsupp.linearCombination_single] using
  congrArg (z • ·) (LinearMap.congr_fun (pI v σ) u)
@[simp] theorem EO (u:Chains B A):realize u (Finsupp.single (ContinuousMap.id A) 1) = u:=by
 simp [realize,post]; exact Finsupp.mapDomain_id
theorem AS {E:Type*} [TopologicalSpace E]
  (v:Chains D B) (u:Chains B A) (v':Chains D E) (u':Chains E A)
  (h:realize v (realize u (Finsupp.single (ContinuousMap.id A) 1)) =
   realize v' (realize u' (Finsupp.single (ContinuousMap.id A) 1))) :
  (realize (X:=X) v).comp (realize u) = (realize v').comp (realize u'):=by
 rw [realize_comp,realize_comp]
 apply congrArg realize
 simpa only [EO] using h
end
def eW (σ:c4 X) (a:I):a5 X:=⟨fun t=>σ (a,t),by fun_prop⟩
def e4 (σ:c4 X) (a:I):a5 X:=⟨fun t=>σ (t,a),by fun_prop⟩
def vN (σ:i2 X) (a:I):c4 X:=⟨fun t=>σ (a,t),by fun_prop⟩
def vO (σ:i2 X) (a:I):c4 X:=⟨fun t=>σ (t.1,a,t.2),by fun_prop⟩
def vP (σ:i2 X) (a:I):c4 X:=⟨fun t=>σ (t.1,t.2,a),by fun_prop⟩
def b₁:C₁ X →ₗ[ℤ] C₀ X:=Finsupp.linearCombination ℤ
 (fun σ=>Finsupp.single (σ 1) 1 - Finsupp.single (σ 0) 1)
def oT:C₁ (I × I):=
 let σ:=ContinuousMap.id (I × I)
 Finsupp.single (eW σ 1) 1 - Finsupp.single (eW σ 0) 1 -
  Finsupp.single (e4 σ 1) 1 + Finsupp.single (e4 σ 0) 1
def oM:C₂ (I × I × I):=
 let σ:=ContinuousMap.id (I × I × I)
 Finsupp.single (vN σ 1) 1 - Finsupp.single (vN σ 0) 1 -
  Finsupp.single (vO σ 1) 1 + Finsupp.single (vO σ 0) 1 +
  Finsupp.single (vP σ 1) 1 - Finsupp.single (vP σ 0) 1
def b₂:C₂ X →ₗ[ℤ] C₁ X:=realize oT
def b₃:C₃ X →ₗ[ℤ] C₂ X:=realize oM
@[simp] theorem KI (σ:a5 X) (a:ℤ) :
  b₁ (Finsupp.single σ a)=a • (Finsupp.single (σ 1) 1 - Finsupp.single (σ 0) 1):=by
 simp [b₁]
@[simp] theorem Jy (σ:c4 X) (a:ℤ) :
  b₂ (Finsupp.single σ a)=a • (Finsupp.single (eW σ 1) 1 -
   Finsupp.single (eW σ 0) 1 - Finsupp.single (e4 σ 1) 1 + Finsupp.single (e4 σ 0) 1):=by
 simp [b₂,realize,oT]; rfl
@[simp] theorem O4 (σ:i2 X) (a:ℤ) :
  b₃ (Finsupp.single σ a)=a • (Finsupp.single (vN σ 1) 1 -
   Finsupp.single (vN σ 0) 1 - Finsupp.single (vO σ 1) 1 +
   Finsupp.single (vO σ 0) 1 + Finsupp.single (vP σ 1) 1 - Finsupp.single (vP σ 0) 1):=by
 simp [b₃,realize,oM]; rfl
theorem WO:(b₁:C₁ X →ₗ[ℤ] C₀ X).comp b₂=0:=by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,Jy,one_smul,map_add,map_sub,map_smul,KI,eW,e4,
    ContinuousMap.coe_mk,LinearMap.zero_apply]
  abel_nf
@[simp] theorem WQ (σ:i2 X) (a b:I):eW (vO σ a) b=eW (vN σ b) a:=rfl
@[simp] theorem WR (σ:i2 X) (a b:I):eW (vP σ a) b=e4 (vN σ b) a:=rfl
@[simp] theorem WS (σ:i2 X) (a b:I):e4 (vP σ a) b=e4 (vO σ b) a:=rfl
theorem WT:(b₂:C₂ X →ₗ[ℤ] C₁ X).comp b₃=0:=by
  apply Finsupp.lhom_ext
  intro σ a
  simp only [LinearMap.comp_apply,O4,one_smul,map_add,map_sub,map_smul,Jy,
    WQ,WR,WS,LinearMap.zero_apply]
  abel_nf
def gQ (x:X):a5 X:=ContinuousMap.const _ x
def lH (σ:a5 X):c4 X:=⟨fun t=>σ t.1,by fun_prop⟩
def kN (σ:a5 X):c4 X:=⟨fun t=>σ t.2,by fun_prop⟩
@[simp] theorem dl3 (σ:a5 X) (a:I) :
  eW (lH σ) a=gQ (σ a):=ContinuousMap.ext (fun _=>rfl)
@[simp] theorem dk9 (σ:a5 X) (a:I) :
  e4 (lH σ) a=σ:=ContinuousMap.ext (fun _=>rfl)
@[simp] theorem dl2 (σ:a5 X) (a:I) :
  eW (kN σ) a=σ:=ContinuousMap.ext (fun _=>rfl)
@[simp] theorem dl6 (σ:a5 X) (a:I) :
  e4 (kN σ) a=gQ (σ a):=ContinuousMap.ext (fun _=>rfl)
def D₁ (X:Type*) [TopologicalSpace X]:Submodule ℤ (C₁ X):=
 Submodule.span ℤ (Set.range (fun x:X=>Finsupp.single (gQ x) 1))
def D₂ (X:Type*) [TopologicalSpace X]:Submodule ℤ (C₂ X):=
 Submodule.span ℤ (Set.range (fun σ:a5 X=>Finsupp.single (lH σ) 1) ∪
  Set.range (fun σ:a5 X=>Finsupp.single (kN σ) 1))
abbrev N₁ (X:Type*) [TopologicalSpace X]:=C₁ X ⧸ D₁ X
abbrev N₂ (X:Type*) [TopologicalSpace X]:=C₂ X ⧸ D₂ X
theorem WV:D₁ X <= LinearMap.ker (b₁:C₁ X →ₗ[ℤ] C₀ X):=by
 apply Submodule.span_le.mpr
 rintro _ ⟨x,rfl⟩
 simp [gQ]
theorem Nl:D₂ X <= (D₁ X).comap (b₂:C₂ X →ₗ[ℤ] C₁ X):=by
 apply Submodule.span_le.mpr
 rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩)
 ·change b₂ (Finsupp.single (lH σ) 1) ∈ D₁ X
  have h₁ (x:X):Finsupp.single (gQ x) 1 ∈ D₁ X:=
   Submodule.subset_span ⟨x,rfl⟩
  simpa using (D₁ X).sub_mem (h₁ (σ 1)) (h₁ (σ 0))
 ·change b₂ (Finsupp.single (kN σ) 1) ∈ D₁ X
  have h₁ (x:X):Finsupp.single (gQ x) 1 ∈ D₁ X:=
   Submodule.subset_span ⟨x,rfl⟩
  have he:b₂ (Finsupp.single (kN σ) 1) =
    Finsupp.single (gQ (σ 0)) 1 - Finsupp.single (gQ (σ 1)) 1:=by
   simp [sub_eq_add_neg]
   abel
  rw [he]
  exact (D₁ X).sub_mem (h₁ (σ 0)) (h₁ (σ 1))
def d₁:N₁ X →ₗ[ℤ] C₀ X:=(D₁ X).liftQ b₁ WV
def d₂:N₂ X →ₗ[ℤ] N₁ X:=(D₂ X).mapQ (D₁ X) b₂ Nl
def d₃:C₃ X →ₗ[ℤ] N₂ X:=(D₂ X).mkQ.comp b₃
@[simp] theorem O5 (c:C₁ X):d₁ ((D₁ X).mkQ c)=b₁ c:=rfl
@[simp] theorem dt8 (c:C₂ X):d₂ ((D₂ X).mkQ c)=(D₁ X).mkQ (b₂ c):=rfl
theorem O6 (c:N₂ X):d₁ (d₂ c)=0:=by
 obtain ⟨c,rfl⟩:=Submodule.mkQ_surjective (D₂ X) c
 exact LinearMap.congr_fun WO c
theorem WX (c:C₃ X):d₂ (d₃ c)=0:=by
 change (D₁ X).mkQ ((b₂:C₂ X →ₗ[ℤ] C₁ X) (b₃ c))=0
 have h:=LinearMap.congr_fun WT c
 change b₂ (b₃ c)=0 at h
 rw [h]
 exact map_zero _
def C4 (f:C(X,Y)):C₀ X →ₗ[ℤ] C₀ Y:=Finsupp.lmapDomain ℤ ℤ (f)
abbrev lZ (f:C(X,Y)):C₁ X →ₗ[ℤ] C₁ Y:=post f
abbrev nQ (f:C(X,Y)):C₂ X →ₗ[ℤ] C₂ Y:=post f
abbrev Nm (f:C(X,Y)):C₃ X →ₗ[ℤ] C₃ Y:=post f
@[simp] theorem dt4 (f:C(X,Y)) (x:X) (a:ℤ) :
  C4 f (Finsupp.single x a)=Finsupp.single (f x) a:=by simp [C4]
theorem WZ (f:C(X,Y)):b₁.comp (lZ f)=(C4 f).comp b₁:=by
 apply Finsupp.lhom_ext
 intro σ a
 simp
theorem W0 (f:C(X,Y)):b₂.comp (nQ f)=(lZ f).comp b₂:=pI _ _
section Prism
variable {D E:Type*} [TopologicalSpace D] [TopologicalSpace E]
variable {f g:C(X,Y)} (H:f.Homotopy g)
def slice {D:Type*} [TopologicalSpace D] (σ:C(I × D,X)) (a:I):C(D,X):=⟨fun t=>σ (a,t),by fun_prop⟩
def l6 (σ:C(D,X)):C(I × D,Y):=⟨fun t=>H (t.1,σ t.2),by fun_prop⟩
theorem La (σ:C(D,X)) (e:C(E,D)) :
  (l6 H σ).comp ((ContinuousMap.id I).prodMap e) = l6 H (σ.comp e):=rfl
@[simp] theorem Np (σ:C(D,X)):slice (l6 H σ) 0 = f.comp σ:=
 ContinuousMap.ext (fun _=>H.apply_zero _)
@[simp] theorem O7 (σ:C(D,X)):slice (l6 H σ) 1 = g.comp σ:=
 ContinuousMap.ext (fun _=>H.apply_one _)
def P:Chains D X →ₗ[ℤ] Chains (I × D) Y:=Finsupp.lmapDomain ℤ ℤ (l6 H)
@[simp] theorem Kh (σ:C(D,X)) (z:ℤ) :
  P H (Finsupp.single σ z) = Finsupp.single (l6 H σ) z:=by simp [P]
def track (x:X):a5 Y:=
 (l6 H (ContinuousMap.const Unit x)).comp ⟨fun t=>(t,()),by fun_prop⟩
theorem W2:D₁ X ≤ (D₂ Y).comap (P H):=by
 apply Submodule.span_le.mpr
 rintro _ ⟨x,rfl⟩
 change P H (Finsupp.single (gQ x) 1) ∈ D₂ Y
 rw [Kh]
 exact Submodule.subset_span (Or.inl ⟨track H x,rfl⟩)
end Prism
@[simp] theorem Gb {D:Type*} [TopologicalSpace D] :
  post (A:=D) (ContinuousMap.id X)=LinearMap.id:=by ext; simp
private theorem DU {D:Type*} [TopologicalSpace D] (U:Submodule ℤ (Chains D Y))
  (x:Y) (h:Finsupp.single (ContinuousMap.const D x) 1 ∈ U) (c:Chains D X) :
  post (ContinuousMap.const X x) c ∈ U:=by
 induction c using Finsupp.induction_linear with
 | zero=>simp
 | add c d hc hd=>simpa only [map_add] using U.add_mem hc hd
 | single σ a=>
  rw [nY,← Finsupp.smul_single_one]
  exact U.smul_mem a h
theorem O8 (x:Y) (c:C₁ X):lZ (ContinuousMap.const X x) c ∈ D₁ Y:=
 DU (D₁ Y) x (Submodule.subset_span ⟨x,rfl⟩) c
theorem cs2 (x:Y) (c:C₂ X):nQ (ContinuousMap.const X x) c ∈ D₂ Y:=
 DU (D₂ Y) x (Submodule.subset_span (Or.inl ⟨gQ x,rfl⟩)) c
/-- Project the l6 identity before discarding the constant end and the sides. -/
private theorem Cd {D M:Type*} [TopologicalSpace D] [AddCommGroup M] [Module ℤ M]
  {x:X} (H:(ContinuousMap.id X).Homotopy (ContinuousMap.const X x))
  (b:Chains (I × D) X →ₗ[ℤ] Chains D X) (s:Chains D X →ₗ[ℤ] Chains D X)
  (q:Chains D X →ₗ[ℤ] M) (c:Chains D X)
  (faces:b.comp (P H) + s = post (ContinuousMap.const X x) - LinearMap.id)
  (side:q (s c)=0) (cap:q (post (ContinuousMap.const X x) c)=0) :
  q (b (-P H c)) = q c:=by
 have h:=congrArg q (LinearMap.congr_fun faces c)
 simpa [side,cap] using congrArg Neg.neg h

theorem r0 [ContractibleSpace X] (c:N₁ X) (hc:d₁ c=0) :
  ∃ b:N₂ X,d₂ b=c:=by
 obtain ⟨x,⟨H⟩⟩:=id_nullhomotopic X
 obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective c
 change b₁ c=0 at hc
 let T:=Finsupp.lmapDomain ℤ ℤ (track H)
 refine ⟨(D₂ X).mkQ (-P H c),Cd H b₂ (T.comp b₁) (D₁ X).mkQ c ?_ ?_
  ((Submodule.Quotient.mk_eq_zero _).mpr (O8 x c))⟩
 ·apply Finsupp.lhom_ext
  intro σ z
  have front (t:I):eW (l6 H σ) t = slice (l6 H σ) t:=rfl
  have side (t:I):e4 (l6 H σ) t = track H (σ t):=rfl
  have tr (v:X) (a:ℤ):T (Finsupp.single v a) = Finsupp.single (track H v) a:=by simp [T]
  simp [front,side,tr,smul_add,smul_sub,Finsupp.smul_single]
 ·simp [hc]
theorem r7 [ContractibleSpace X] (c:N₂ X) (hc:d₂ c=0) :
  ∃ b:C₃ X,d₃ b=c:=by
 obtain ⟨x,⟨H⟩⟩:=id_nullhomotopic X
 obtain ⟨c,rfl⟩:=(D₂ X).mkQ_surjective c
 refine ⟨-P H c,Cd H b₃ ((P H).comp b₂) (D₂ X).mkQ c ?_
  ((Submodule.Quotient.mk_eq_zero _).mpr (W2 H ((Submodule.Quotient.mk_eq_zero _).mp hc)))
  ((Submodule.Quotient.mk_eq_zero _).mpr (cs2 x c))⟩
 apply Finsupp.lhom_ext
 intro σ z
 have front (t:I):vN (l6 H σ) t = slice (l6 H σ) t:=rfl
 have left (t:I):vO (l6 H σ) t = l6 H (eW σ t):=rfl
 have right (t:I):vP (l6 H σ) t = l6 H (e4 σ t):=rfl
 simp [front,left,right,smul_add,smul_sub,Finsupp.smul_single]
@[simp] theorem W3 (f:C(X,Y)) (x:X) :
  f.comp (gQ x)=gQ (f x):=ContinuousMap.ext (fun _=>rfl)
@[simp] theorem W5 (f:C(X,Y)) (σ:a5 X) :
  f.comp (lH σ)=lH (f.comp σ):=rfl
@[simp] theorem W7 (f:C(X,Y)) (σ:a5 X) :
  f.comp (kN σ)=kN (f.comp σ):=rfl
theorem W8 (f:C(X,Y)):D₁ X <= (D₁ Y).comap (lZ f):=by
 apply Submodule.span_le.mpr
 rintro _ ⟨x,rfl⟩
 change lZ f (Finsupp.single (gQ x) 1) ∈ D₁ Y
 simp only [nY,W3]
 exact Submodule.subset_span ⟨_,rfl⟩
theorem W9 (f:C(X,Y)):D₂ X <= (D₂ Y).comap (nQ f):=by
 apply Submodule.span_le.mpr
 rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩)
 ·change nQ f (Finsupp.single (lH σ) 1) ∈ D₂ Y
  simp only [nY,W5]
  exact Submodule.subset_span (Or.inl ⟨_,rfl⟩)
 ·change nQ f (Finsupp.single (kN σ) 1) ∈ D₂ Y
  simp only [nY,W7]
  exact Submodule.subset_span (Or.inr ⟨_,rfl⟩)
def c3 (f:C(X,Y)):N₁ X →ₗ[ℤ] N₁ Y:=(D₁ X).mapQ (D₁ Y) (lZ f) (W8 f)
def e9 (f:C(X,Y)):N₂ X →ₗ[ℤ] N₂ Y:=(D₂ X).mapQ (D₂ Y) (nQ f) (W9 f)
@[simp] theorem Mb (f:C(X,Y)) (c:C₁ X) :
  c3 f ((D₁ X).mkQ c)=(D₁ Y).mkQ (lZ f c):=rfl
@[simp] theorem Mc (f:C(X,Y)) (c:C₂ X) :
  e9 f ((D₂ X).mkQ c)=(D₂ Y).mkQ (nQ f c):=rfl
theorem Md (f:C(X,Y)) (c:N₁ X):d₁ (c3 f c)=C4 f (d₁ c):=by
 obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective c
 exact LinearMap.congr_fun (WZ f) c
theorem Gd (f:C(X,Y)) (c:N₂ X):d₂ (e9 f c)=c3 f (d₂ c):=by
 obtain ⟨c,rfl⟩:=(D₂ X).mkQ_surjective c
 change (D₁ Y).mkQ (b₂ (nQ f c))=(D₁ Y).mkQ (lZ f (b₂ c))
 exact congrArg (D₁ Y).mkQ (LinearMap.congr_fun (W0 f) c)
theorem Me (g:C(Y,Z)) (f:C(X,Y)) (c:N₁ X) :
  c3 (g.comp f) c=c3 g (c3 f c):=by
 obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective c
 simp only [Mb,post_comp,LinearMap.comp_apply]
theorem Xb (g:C(Y,Z)) (f:C(X,Y)) (c:N₂ X) :
  e9 (g.comp f) c=e9 g (e9 f c):=by
 obtain ⟨c,rfl⟩:=(D₂ X).mkQ_surjective c
 simp only [Mc,post_comp,LinearMap.comp_apply]
@[simp] theorem O9 (c:N₁ X):c3 (ContinuousMap.id X) c=c:=by
 obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective c
 rw [Mb,lZ,Gb]
 rfl
@[simp] theorem dw7 (c:N₂ X):e9 (ContinuousMap.id X) c=c:=by
 obtain ⟨c,rfl⟩:=(D₂ X).mkQ_surjective c
 rw [Mc,nQ,Gb]
 rfl
@[simp] theorem db6 (y:Y) (c:N₁ X):c3 (ContinuousMap.const X y) c=0:=by
 obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective c
 exact (Submodule.Quotient.mk_eq_zero _).mpr (O8 y c)
@[simp] theorem dt5 (y:Y) (c:N₂ X):e9 (ContinuousMap.const X y) c=0:=by
 obtain ⟨c,rfl⟩:=(D₂ X).mkQ_surjective c
 exact (Submodule.Quotient.mk_eq_zero _).mpr (cs2 y c)
end EilenbergGanea.CubicalSingular
namespace EilenbergGanea.CubicalSingular
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
def half (b:Bool):C(I,I) where
 toFun t:=if b then ⟨(1 + t.val) / 2,by constructor <;> linarith [t.property.1,t.property.2]⟩
  else ⟨t.val / 2,by constructor <;> linarith [t.property.1,t.property.2]⟩
 continuous_toFun:=by cases b <;> dsimp <;> fun_prop
@[simp] theorem j3:half false 0=0:=Subtype.ext (by norm_num [half])
@[simp] theorem m4:half true 1=1:=Subtype.ext (by norm_num [half])
theorem EU:half false 1=half true 0:=Subtype.ext (by norm_num [half])
def wO {D κ:Type*} [TopologicalSpace D] (a:κ → C(D,D))
  (b:Bool × κ):C(I × D,I × D):=(half b.1).prodMap (a b.2)
abbrev r9:=wO half
abbrev Ee:=wO r9
def jG (σ:a5 X) (i:Bool):a5 X:=σ.comp (half i)
def v7 (σ:c4 X) (i j:Bool):c4 X:=σ.comp (r9 (i,j))
def EW (σ:i2 X) (i j k:Bool):i2 X:=σ.comp (Ee (i,j,k))
def tiles {D κ:Type*} [TopologicalSpace D] [Fintype κ] (a:κ → C(D,D)):Chains D D:=
 ∑ i,Finsupp.single (a i) 1
def S₁:C₁ X →ₗ[ℤ] C₁ X:=realize (tiles half)
def S₂:C₂ X →ₗ[ℤ] C₂ X:=realize (tiles r9)
def S₃:C₃ X →ₗ[ℤ] C₃ X:=realize (tiles Ee)
@[simp] theorem Pd (σ:a5 X) (a:ℤ) :
  S₁ (Finsupp.single σ a)=∑ i:Bool,Finsupp.single (jG σ i) a:=by
 simp [S₁,realize,tiles,Finsupp.smul_single,jG]
@[simp] theorem Pe (σ:c4 X) (a:ℤ) :
  S₂ (Finsupp.single σ a)=∑ i:Bool,∑ j:Bool,Finsupp.single (v7 σ i j) a:=by
 simp [S₂,realize,tiles,Fintype.sum_prod_type,Finsupp.smul_single,v7]
@[simp] theorem Xc (σ:i2 X) (a:ℤ) :
  S₃ (Finsupp.single σ a)=∑ i:Bool,∑ j:Bool,∑ k:Bool,Finsupp.single (EW σ i j k) a:=by
 simp [S₃,realize,tiles,Fintype.sum_prod_type,Finsupp.smul_single,EW]
@[simp] theorem Ph (σ:c4 X) (i j:Bool) (a:I) :
  eW (v7 σ i j) a=jG (eW σ (half i a)) j:=rfl
@[simp] theorem Pk (σ:c4 X) (i j:Bool) (a:I) :
  e4 (v7 σ i j) a=jG (e4 σ (half j a)) i:=rfl
@[simp] theorem Xd (σ:i2 X) (i j k:Bool) (a:I) :
  vN (EW σ i j k) a=v7 (vN σ (half i a)) j k:=rfl
@[simp] theorem Xf (σ:i2 X) (i j k:Bool) (a:I) :
  vO (EW σ i j k) a=v7 (vO σ (half j a)) i k:=rfl
@[simp] theorem Xg (σ:i2 X) (i j k:Bool) (a:I) :
  vP (EW σ i j k) a=v7 (vP σ (half k a)) i j:=rfl
theorem Xh:b₁.comp (S₁:C₁ X →ₗ[ℤ] C₁ X)=b₁:=by
 apply Finsupp.lhom_ext
 intro σ a
 simp [jG,EU,smul_sub,Finsupp.smul_single]
theorem Dt:b₂.comp (S₂:C₂ X →ₗ[ℤ] C₂ X)=S₁.comp b₂:=by
 apply AS oT (tiles r9) (tiles half) oT
 change b₂ (S₂ _) = S₁ (b₂ _)
 simp only [Pe,Pd,Jy,Ph,Pk,Fintype.sum_bool,map_add,map_sub,one_smul,j3,m4,EU]
 abel
theorem Dv:b₃.comp (S₃:C₃ X →ₗ[ℤ] C₃ X)=S₂.comp b₃:=by
 apply AS oM (tiles Ee) (tiles r9) oM
 change b₃ (S₃ _) = S₂ (b₃ _)
 simp only [Xc,Pe,O4,Xd,Xf,Xg,Fintype.sum_bool,map_add,map_sub,one_smul,j3,m4,EU]
 abel
theorem Xj (f:C(X,Y)):S₁.comp (lZ f)=(lZ f).comp S₁:=pI _ _
theorem Xk (f:C(X,Y)):S₂.comp (nQ f)=(nQ f).comp S₂:=pI _ _
def KO (X:Type*) [TopologicalSpace X]:Set (a5 X):=Set.range gQ
def Pq (X:Type*) [TopologicalSpace X]:Set (c4 X):=
 Set.range lH ∪ Set.range kN
theorem qW:D₁ X=Finsupp.supported ℤ ℤ (KO X):=by
 rw [Finsupp.supported_eq_span_single]
 unfold D₁ KO
 congr 1
 ext c
 simp only [Set.mem_range,Set.mem_image]
 aesop
theorem AY:D₂ X=Finsupp.supported ℤ ℤ (Pq X):=by
 rw [Finsupp.supported_eq_span_single]
 unfold D₂ Pq
 rw [Set.image_union]
 congr 1
 ext c
 simp only [Set.mem_union,Set.mem_range,Set.mem_image]
 aesop
private theorem Ci {D κ:Type*} [TopologicalSpace D] [Fintype κ]
  (a:κ → C(D,D)) {s t:Set C(D,X)} (h:∀ σ ∈ s,∀ i,σ.comp (a i) ∈ t) :
  Finsupp.supported ℤ ℤ s ≤ (Finsupp.supported ℤ ℤ t).comap (realize (tiles a)):=by
 rw [Finsupp.supported_eq_span_single,Submodule.span_le]
 rintro _ ⟨σ,hσ,rfl⟩
 change realize (tiles a) (Finsupp.single σ 1) ∈ Finsupp.supported ℤ ℤ t
 simpa [realize,tiles] using Submodule.sum_mem (Finsupp.supported ℤ ℤ t)
  (fun i (_:i ∈ Finset.univ)=>Finsupp.single_mem_supported ℤ (1:ℤ) (h σ hσ i))
theorem Xl:D₁ X <= (D₁ X).comap S₁:=by
 rw [qW]
 apply Ci
 rintro _ ⟨x,rfl⟩ i
 exact ⟨x,rfl⟩
theorem Xm:D₂ X <= (D₂ X).comap S₂:=by
 rw [AY]
 apply Ci
 rintro _ (⟨σ,rfl⟩ | ⟨σ,rfl⟩) ⟨i,j⟩
 ·exact Or.inl ⟨jG σ i,rfl⟩
 ·exact Or.inr ⟨jG σ j,rfl⟩
def k3:N₁ X →ₗ[ℤ] N₁ X:=(D₁ X).mapQ (D₁ X) S₁ Xl
def j4:N₂ X →ₗ[ℤ] N₂ X:=(D₂ X).mapQ (D₂ X) S₂ Xm
@[simp] theorem Xn (c:C₁ X):k3 ((D₁ X).mkQ c)=(D₁ X).mkQ (S₁ c):=rfl
@[simp] theorem Xo (c:C₂ X):j4 ((D₂ X).mkQ c)=(D₂ X).mkQ (S₂ c):=rfl
theorem Pv (c:N₁ X):d₁ (k3 c)=d₁ c:=by
 obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective c
 exact LinearMap.congr_fun Xh c
theorem Xp (c:N₂ X):d₂ (j4 c)=k3 (d₂ c):=by
 obtain ⟨c,rfl⟩:=(D₂ X).mkQ_surjective c
 change (D₁ X).mkQ (b₂ (S₂ c))=(D₁ X).mkQ (S₁ (b₂ c))
 exact congrArg (D₁ X).mkQ (LinearMap.congr_fun Dt c)
theorem Xq (c:C₃ X):d₃ (S₃ c)=j4 (d₃ c):=by
 change (D₂ X).mkQ (b₃ (S₃ c))=(D₂ X).mkQ (S₂ (b₃ c))
 exact congrArg (D₂ X).mkQ (LinearMap.congr_fun Dv c)
theorem Pw (f:C(X,Y)) (c:N₁ X):k3 (c3 f c)=c3 f (k3 c):=by
 obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective c
 change (D₁ Y).mkQ (S₁ (lZ f c))=(D₁ Y).mkQ (lZ f (S₁ c))
 exact congrArg (D₁ Y).mkQ (LinearMap.congr_fun (Xj f) c)
theorem Xr (f:C(X,Y)) (c:N₂ X):j4 (e9 f c)=e9 f (j4 c):=by
 obtain ⟨c,rfl⟩:=(D₂ X).mkQ_surjective c
 change (D₂ Y).mkQ (S₂ (nQ f c))=(D₂ Y).mkQ (nQ f (S₂ c))
 exact congrArg (D₂ Y).mkQ (LinearMap.congr_fun (Xk f) c)
end EilenbergGanea.CubicalSingular
namespace EilenbergGanea.CubicalSingular
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
def gen₁ (σ:a5 X):N₁ X:=(D₁ X).mkQ (Finsupp.single σ 1)
def gen₂ (σ:c4 X):N₂ X:=(D₂ X).mkQ (Finsupp.single σ 1)
@[simp] theorem KQ (f:C(X,Y)) (σ:a5 X):c3 f (gen₁ σ)=gen₁ (f.comp σ):=by
 rw [gen₁,Mb,nY]
 rfl
@[simp] theorem Xt (f:C(X,Y)) (σ:c4 X):e9 f (gen₂ σ)=gen₂ (f.comp σ):=by
 rw [gen₂,Mc,nY]
 rfl
local instance:ContractibleSpace I:=
 (convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
def oN:N₂ I:=
 (r0 (k3 (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I))
  (by rw [map_sub,Pv,sub_self])).choose
theorem Xv:d₂ oN =
  k3 (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I):=
 (r0 (k3 (gen₁ (ContinuousMap.id I)) - gen₁ (ContinuousMap.id I))
  (by rw [map_sub,Pv,sub_self])).choose_spec
def wP:C₁ X →ₗ[ℤ] N₂ X:=Finsupp.linearCombination ℤ
 (fun σ=>e9 σ oN)
@[simp] theorem Py (σ:a5 X) (a:ℤ) :
  wP (Finsupp.single σ a)=a • e9 σ oN:=by simp [wP]
theorem Xw:D₁ X <= LinearMap.ker wP:=by
 apply Submodule.span_le.mpr
 rintro _ ⟨x,rfl⟩
 change wP (Finsupp.single (gQ x) 1)=0
 simp [gQ]
def H₁:N₁ X →ₗ[ℤ] N₂ X:=(D₁ X).liftQ wP Xw
@[simp] theorem dy0 (c:C₁ X):H₁ ((D₁ X).mkQ c)=wP c:=rfl
theorem yD (c:N₁ X):d₂ (H₁ c)=k3 c - c:=by
  obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective c
  have he:d₂.comp (wP:C₁ X →ₗ[ℤ] N₂ X) =
      (k3 - LinearMap.id).comp (D₁ X).mkQ:=by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply,Py,map_smul,Gd,Xv,
      map_sub,<- Pw,KQ,ContinuousMap.comp_id]
    change a • (k3 (gen₁ σ) - gen₁ σ)=k3 ((D₁ X).mkQ (Finsupp.single σ a)) -
      (D₁ X).mkQ (Finsupp.single σ a)
    rw [<- Finsupp.smul_single_one σ a,map_smul,map_smul,smul_sub]
    rfl
  exact LinearMap.congr_fun he c
end EilenbergGanea.CubicalSingular
namespace EilenbergGanea.CubicalSingular
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
def jV (D:Type*) [TopologicalSpace D] (U:Set X):Set C(D,X):=
 {σ | Set.range σ ⊆ U}
theorem Xx {D:Type*} [TopologicalSpace D] {U V:Set X} (h:U ⊆ V) :
  jV D U ⊆ jV D V:=fun _ hσ=>hσ.trans h
@[simp] theorem Mh (D:Type*) [TopologicalSpace D] (U V:Set X) :
  jV D (U ∩ V)=jV D U ∩ jV D V:=by
 ext σ
 exact Set.subset_inter_iff
@[simp] theorem Pz (D:Type*) [TopologicalSpace D] :
  jV D (Set.univ:Set X)=Set.univ:=by ext; simp [jV]
def inc (U:Set X):C(U,X):=⟨Subtype.val,continuous_subtype_val⟩
theorem Xy (D:Type*) [TopologicalSpace D] (U:Set X) :
  Set.range (fun σ:C(D,U)=>(inc U).comp σ)=jV D U:=by
 ext σ
 constructor
 ·rintro ⟨σ,rfl⟩ _ ⟨t,rfl⟩
  exact (σ t).property
 ·intro hσ
  refine ⟨⟨fun t=>⟨σ t,hσ ⟨t,rfl⟩⟩,σ.continuous.subtype_mk _⟩,?_⟩
  rfl
def L₀ (U:Set X):Submodule ℤ (C₀ X):=Finsupp.supported ℤ ℤ U
def IU (U:Set X):Submodule ℤ (C₁ X):=Finsupp.supported ℤ ℤ (jV I U)
def Dw (U:Set X):Submodule ℤ (C₂ X):=Finsupp.supported ℤ ℤ (jV (I × I) U)
def L₁ (U:Set X):Submodule ℤ (N₁ X):=(IU U).map (D₁ X).mkQ
def L₂ (U:Set X):Submodule ℤ (N₂ X):=(Dw U).map (D₂ X).mkQ
def L₃ (U:Set X):Submodule ℤ (C₃ X):=Finsupp.supported ℤ ℤ (jV (I × I × I) U)
section
variable {A:Type*} (D:Set A)
private abbrev Bw:=(Finsupp.lsubtypeDomain Dᶜ:(A →₀ ℤ) →ₗ[ℤ] (↥Dᶜ →₀ ℤ))
private theorem Gh:Finsupp.supported ℤ ℤ D = (Bw D).ker:=by
 ext x
 exact (Finsupp.mem_supported' ℤ x).trans Finsupp.subtypeDomain_eq_zero_iff'.symm
noncomputable def EY:((A →₀ ℤ) ⧸ Finsupp.supported ℤ ℤ D) ≃ₗ[ℤ] (↥Dᶜ →₀ ℤ):=
 LinearEquiv.ofBijective (_root_.Submodule.liftQ _ (Bw D) (Gh D).le) ⟨
  LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot' _ _ (Gh D)),
  fun x=>⟨(Finsupp.supported ℤ ℤ D).mkQ x.extendDomain,Finsupp.subtypeDomain_extendDomain x⟩⟩
theorem EZ (s:Set A):(Finsupp.supported ℤ ℤ s).map (Finsupp.supported ℤ ℤ D).mkQ =
    (Finsupp.supported ℤ ℤ (Subtype.val ⁻¹' s:Set ↥Dᶜ)).comap (EY D).toLinearMap:=by
  apply Submodule.comap_injective_of_surjective (Finsupp.supported ℤ ℤ D).mkQ_surjective
  rw [Submodule.comap_map_eq,Submodule.ker_mkQ,← Finsupp.supported_union]
  ext x
  change x ∈ Finsupp.supported ℤ ℤ _ ↔ (Bw D) x ∈ Finsupp.supported ℤ ℤ _
  simp only [Finsupp.mem_supported',Set.mem_union,Set.mem_preimage,Bw,
    Finsupp.lsubtypeDomain_apply,Finsupp.subtypeDomain_apply,Subtype.forall,Set.mem_compl_iff]
  grind
theorem C5 (P:Submodule ℤ (A →₀ ℤ)) (h:P = Finsupp.supported ℤ ℤ D) (s t:Set A) :
  (Finsupp.supported ℤ ℤ (s ∩ t)).map P.mkQ =
  (Finsupp.supported ℤ ℤ s).map P.mkQ ⊓
  (Finsupp.supported ℤ ℤ t).map P.mkQ:=by
 subst P
 simp only [EZ]
 rw [ Set.preimage_inter,Finsupp.supported_inter,Submodule.comap_inf]
end
omit [TopologicalSpace X] in
@[simp] theorem dw9 (U V:Set X):L₀ (U ∩ V)=L₀ U ⊓ L₀ V:=Finsupp.supported_inter _ _
@[simp] theorem dm1 (U V:Set X):L₁ (U ∩ V)=L₁ U ⊓ L₁ V:=by
 unfold L₁ IU
 rw [Mh]
 exact C5 _ _ qW _ _
@[simp] theorem Xz (U V:Set X):L₂ (U ∩ V)=L₂ U ⊓ L₂ V:=by
 unfold L₂ Dw
 rw [Mh]
 exact C5 _ _ AY _ _
@[simp] theorem dx0 (U V:Set X):L₃ (U ∩ V)=L₃ U ⊓ L₃ V:=by
 unfold L₃
 rw [Mh,Finsupp.supported_inter]
theorem XB {U V:Set X} (h:U ⊆ V):L₁ U <= L₁ V:=
 Submodule.map_mono (Finsupp.supported_mono (Xx h))
end EilenbergGanea.CubicalSingular
open Classical Set
namespace EilenbergGanea.NormalizedSupport
variable {A:Type*}
variable {B:Type*}
theorem XC (f:A -> B) (hf:Function.Injective f) (s:Set B) :
  (Finsupp.supported ℤ ℤ s).comap (Finsupp.lmapDomain ℤ ℤ f) =
   Finsupp.supported ℤ ℤ (f ⁻¹' s):=by
 ext c
 change Finsupp.mapDomain f c ∈ Finsupp.supported ℤ ℤ s ↔
  c ∈ Finsupp.supported ℤ ℤ (f ⁻¹' s)
 rw [Finsupp.mem_supported,Finsupp.mem_supported,Finsupp.mapDomain_support_of_injective hf]
 simp
end EilenbergGanea.NormalizedSupport
namespace EilenbergGanea.CubicalSingular
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
theorem XD {D:Type*} [TopologicalSpace D] (f:C(X,Y))
  (hf:Function.Injective f):Function.Injective (fun σ:C(D,X)=>f.comp σ):=by
 intro σ τ h
 exact ContinuousMap.ext (fun x=>hf (congrArg (fun a:C(D,Y)=>a x) h))
theorem XE (f:C(X,Y)) (hf:Function.Injective f) :
  (fun σ:a5 X=>f.comp σ) ⁻¹' KO Y=KO X:=by
 ext σ
 constructor
 ·rintro ⟨y,hy⟩
  refine ⟨σ 0,ContinuousMap.ext (fun t=>?_)⟩
  apply hf
  have h₀:=congrArg (fun a:a5 Y=>a 0) hy
  have ht:=congrArg (fun a:a5 Y=>a t) hy
  exact h₀.symm.trans ht
 ·rintro ⟨x,rfl⟩
  exact ⟨f x,rfl⟩
theorem XF (f:C(X,Y)) (hf:Function.Injective f) :
  Function.Injective (C4 f):=Finsupp.mapDomain_injective hf
theorem PN (f:C(X,Y)) (hf:Function.Injective f) :
  Function.Injective (c3 f):=by
 apply LinearMap.ker_eq_bot.mp
 change LinearMap.ker ((D₁ X).mapQ (D₁ Y) (lZ f) _)=⊥
 rw [Submodule.ker_mapQ]
 have h:(D₁ Y).comap (lZ f)=D₁ X:=by
  rw [qW,qW]
  unfold lZ post
  rw [NormalizedSupport.XC _ (XD f hf),XE f hf]
 rw [h]
 simp
theorem A8 {D:Type*} [TopologicalSpace D] (U:Set X) :
  (Finsupp.lmapDomain ℤ ℤ (fun σ:C(D,U)=>(inc U).comp σ)).range =
   Finsupp.supported ℤ ℤ (jV D U):=by
 simpa only [Finsupp.supported_univ,Submodule.map_top,Set.image_univ,Xy] using
  Finsupp.lmapDomain_supported ℤ ℤ (fun σ:C(D,U)=>(inc U).comp σ) Set.univ
theorem u9 (U:Set X):(c3 (inc U)).range=L₁ U:=by rw [c3,Submodule.range_mapQ,lZ,post,A8]; rfl
theorem o4 (U:Set X):(e9 (inc U)).range=L₂ U:=by rw [e9,Submodule.range_mapQ,nQ,post,A8]; rfl
theorem PW (U:Set X):L₂ U <= (L₁ U).comap d₂:=by
 rw [← o4,← u9]
 rintro _ ⟨x,rfl⟩
 exact ⟨_,(Gd _ x).symm⟩
theorem P7 (U:Set X):L₃ U <= (L₂ U).comap d₃:=by
 rw [L₃,← A8,← o4]
 rintro _ ⟨x,rfl⟩
 refine ⟨d₃ x,?_⟩
 change (D₂ X).mkQ (nQ _ (b₃ x)) = (D₂ X).mkQ (b₃ (Nm _ x))
 exact congrArg (D₂ X).mkQ (LinearMap.congr_fun (pI oM (inc U)).symm x)
theorem XG (f:C(X,Y)) {U:Set Y} (hf:Set.range f ⊆ U) (c:N₂ X) :
  e9 f c ∈ L₂ U:=by
 let f':C(X,U):=⟨fun x=>⟨f x,hf ⟨x,rfl⟩⟩,f.continuous.subtype_mk _⟩
 have h:f=(inc U).comp f':=rfl
 rw [h,Xb,<- o4]
 exact ⟨e9 f' c,rfl⟩
theorem XH (U:Set X):L₁ U <= (L₂ U).comap H₁:=by
 rw [L₁,IU,Submodule.map_le_iff_le_comap,Finsupp.supported_eq_span_single,Submodule.span_le]
 rintro _ ⟨σ,hσ,rfl⟩
 change wP (Finsupp.single σ 1) ∈ L₂ U
 rw [Py,one_smul]
 exact XG σ hσ _
end EilenbergGanea.CubicalSingular
open Classical Set
namespace EilenbergGanea.CubicalMesh
variable {D X:Type*} [MetricSpace D] [CompactSpace D] [Nonempty D] [TopologicalSpace X]
variable {κ:Type*} [Fintype κ]
abbrev Chains (D X:Type*) [TopologicalSpace D] [TopologicalSpace X]:=C(D,X) →₀ ℤ
def small (U:Set (Set X)):Set C(D,X):={σ | ∃ u ∈ U,Set.range σ ⊆ u}
def wQ (U:Set (Set X)):Submodule ℤ (Chains D X):=Finsupp.supported ℤ ℤ (small U)
def subdivision (a:κ -> C(D,D)):Chains D X →ₗ[ℤ] Chains D X:=
 CubicalSingular.realize (CubicalSingular.tiles a)
omit [CompactSpace D] [Nonempty D] in
@[simp] theorem u4 (a:κ -> C(D,D)) (σ:C(D,X)) (z:ℤ) :
  subdivision a (Finsupp.single σ z)=∑ i,Finsupp.single (σ.comp (a i)) z:=by
 simp [subdivision,CubicalSingular.realize,CubicalSingular.tiles,Finset.smul_sum,Finsupp.smul_single]
def Dx (a:κ → C(D,D)) (U:Set (Set X)):ℕ → C(D,X) → Prop
 | 0,σ=>σ ∈ small U
 | n+1,σ=>∀ i,Dx a U n (σ.comp (a i))
theorem uW (a:κ → C(D,D)) {r:ℝ} (hr0:0 ≤ r) (hr:r < 1)
  (ha:∀ i x y,dist (a i x) (a i y) ≤ r * dist x y) (hD:∀ x y:D,dist x y ≤ 1)
  (U:Set (Set X)) (hU:∀ u ∈ U,IsOpen u) (hcover:⋃₀ U=Set.univ) (σ:C(D,X))
  {Q:ℕ → C(D,X) → Prop} (base:∀ f ∈ small U,Q 0 f)
  (step:∀ n f,(∀ i,Q n (f.comp (a i))) → Q (n+1) f) :
  ∀ᶠ n in Filter.atTop,Q n σ:=by
 obtain ⟨δ,hδ,hLeb⟩:=lebesgue_number_lemma_of_metric (s:=Set.univ)
  (c:=fun u:U=>σ ⁻¹' (u:Set X)) isCompact_univ
  (fun u=>(hU u u.property).preimage σ.continuous) (by
   intro x hx
   have:σ x ∈ ⋃₀ U:=hcover ▸ Set.mem_univ _
   obtain ⟨u,hu,hx⟩:=this
   exact Set.mem_iUnion.mpr ⟨⟨u,hu⟩,hx⟩)
 obtain ⟨N,hN⟩:=exists_pow_lt_of_lt_one hδ hr
 have tiles (n:ℕ) (f:C(D,D)) (L:ℝ) (hL:0 ≤ L)
   (hf:∀ x y,dist (f x) (f y) ≤ L * dist x y) (hlt:L*r^n < δ) :
   Q n (σ.comp f):=by
  induction n generalizing f L with
  | zero=>
   apply base
   let p:D:=Classical.choice inferInstance
   obtain ⟨u,hu⟩:=hLeb (f p) trivial
   refine ⟨u,u.property,?_⟩
   rintro _ ⟨x,rfl⟩
   apply hu
   exact ((hf x p).trans (mul_le_of_le_one_right hL (hD x p))).trans_lt (by simpa using hlt)
  | succ n ih=>
   apply step
   intro i
   apply ih (f.comp (a i)) (L*r) (mul_nonneg hL hr0)
   ·intro x y
    exact (hf _ _).trans ((mul_le_mul_of_nonneg_left (ha i x y) hL).trans_eq (mul_assoc ..).symm)
   ·simpa [pow_succ,mul_assoc,mul_left_comm,mul_comm] using hlt
 apply Filter.eventually_atTop.mpr
 refine ⟨N,fun n hn=>tiles n (ContinuousMap.id D) 1 zero_le_one (by simp) ?_⟩
 simpa using (pow_le_pow_of_le_one hr0 hr.le hn).trans_lt hN
theorem w5 (a:κ -> C(D,D)) {r:ℝ} (hr0:0 <= r) (hr:r < 1)
  (ha:∀ i x y,dist (a i x) (a i y) <= r * dist x y)
  (hD:∀ x y:D,dist x y <= 1)
  (U:Set (Set X)) (hU:∀ u ∈ U,IsOpen u) (hcover:⋃₀ U=Set.univ) (c:Chains D X) :
  ∃ N:ℕ,∀ n,N <= n -> ((subdivision a)^[n]) c ∈ wQ U:=by
 classical
 apply Filter.eventually_atTop.mp
 induction c using Finsupp.induction_linear with
 | zero=>
  exact Filter.Eventually.of_forall fun n=>by
   rw [← Module.End.pow_apply,map_zero]; exact Submodule.zero_mem _
 | add c d hc hd=>
  filter_upwards [hc,hd] with n h₁ h₂
  rw [← Module.End.pow_apply,map_add]
  simp only [Module.End.pow_apply]
  exact Submodule.add_mem _ h₁ h₂
 | single σ z=>
  apply uW a hr0 hr ha hD U hU hcover σ
   (Q:=fun n f=>((subdivision a)^[n]) (Finsupp.single f z) ∈ wQ U)
  ·exact fun _ h=>Finsupp.single_mem_supported _ _ h
  ·intro n f h
   rw [Function.iterate_succ_apply,u4,← Module.End.pow_apply,map_sum]
   simp only [Module.End.pow_apply]
   exact Submodule.sum_mem _ fun i _=>h i
end EilenbergGanea.CubicalMesh
namespace EilenbergGanea.CubicalSingular
variable {X:Type*} [TopologicalSpace X]
theorem Mj (b:Bool) (x y:I):dist (half b x) (half b y)=(1/2:ℝ) * dist x y:=by
 have h:(half b x:ℝ) - (half b y:ℝ)=(1/2:ℝ) * ((x:ℝ) - (y:ℝ)):=by
  cases b <;> simp only [half,Bool.false_eq_true,ite_false,ite_true,ContinuousMap.coe_mk] <;> ring
 change |(half b x:ℝ) - (half b y:ℝ)|=(1/2:ℝ) * |(x:ℝ) - (y:ℝ)|
 rw [h,abs_mul,abs_of_pos (by norm_num:(0:ℝ) < 1/2)]
theorem g7 (x y:I):dist x y <= 1:=by
 rw [Subtype.dist_eq,Real.dist_eq,abs_le]
 constructor <;> linarith [x.property.1,x.property.2,y.property.1,y.property.2]
private theorem A9 {D κ:Type*} [MetricSpace D] {a:κ → C(D,D)}
  (h:∀ b x y,dist (a b x) (a b y) ≤ (1/2:ℝ) * dist x y) (b:Bool × κ) (x y:I × D) :
  dist (wO a b x) (wO a b y) ≤ (1/2:ℝ) * dist x y:=by
 change max (dist (half _ _) (half _ _)) (dist (a _ _) (a _ _)) ≤ _
 rw [Mj,Prod.dist_eq,mul_max_of_nonneg _ _ (by norm_num:(0:ℝ) ≤ 1/2)]
 exact max_le_max le_rfl (h _ _ _)
abbrev Ml:=A9 (fun b x y=>(Mj b x y).le)
abbrev XM:=A9 Ml
theorem small_pair (D:Type*) [MetricSpace D] (U V:Set X) :
    CubicalMesh.small (D:=D) {U,V}=jV D U ∪ jV D V:=by
  ext σ
  simp only [CubicalMesh.small,Set.mem_ofPred_eq,Set.mem_insert_iff,Set.mem_singleton_iff,
    Set.mem_union,jV,exists_eq_or_imp,exists_eq_left]
theorem Aa (U V:Set X) (hU:IsOpen U) (hV:IsOpen V) (hUV:U ∪ V=univ)
  (c:C₂ X):∃ N:ℕ,∀ n,N <= n -> (S₂^[n]) c ∈ Dw U ⊔ Dw V:=by
 have h:=CubicalMesh.w5 r9 (by norm_num:(0:ℝ) <= 1/2) (by norm_num:(1/2:ℝ) < 1)
  Ml (fun x y=>max_le (g7 x.1 y.1) (g7 x.2 y.2)) {U,V}
  (by intro u hu; rcases hu with rfl | hu; exact hU; obtain rfl:=hu; exact hV)
  (by simpa using hUV) c
 simpa only [S₂,CubicalMesh.subdivision,CubicalMesh.wQ,small_pair,Finsupp.supported_union,Dw] using h
theorem Ac (U V:Set X) (hU:IsOpen U) (hV:IsOpen V) (hUV:U ∪ V=univ)
  (c:C₃ X):∃ N:ℕ,∀ n,N <= n -> (S₃^[n]) c ∈ L₃ U ⊔ L₃ V:=by
 have h:=CubicalMesh.w5 Ee (by norm_num:(0:ℝ) <= 1/2) (by norm_num:(1/2:ℝ) < 1)
  XM (fun x y=>max_le (g7 x.1 y.1)
   (max_le (g7 x.2.1 y.2.1) (g7 x.2.2 y.2.2))) {U,V}
  (by intro u hu; rcases hu with rfl | hu; exact hU; obtain rfl:=hu; exact hV)
  (by simpa using hUV) c
 simpa only [S₃,CubicalMesh.subdivision,CubicalMesh.wQ,small_pair,Finsupp.supported_union,L₃] using h
theorem XO (c:C₂ X) (n:ℕ) :
  (j4^[n]) ((D₂ X).mkQ c)=(D₂ X).mkQ ((S₂^[n]) c):=by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [Function.iterate_succ_apply',ih,Xo]
theorem XP (U V:Set X) (hU:IsOpen U) (hV:IsOpen V) (hUV:U ∪ V=univ)
  (c:N₂ X):∃ N:ℕ,∀ n,N <= n -> (j4^[n]) c ∈ L₂ U ⊔ L₂ V:=by
 obtain ⟨c,rfl⟩:=(D₂ X).mkQ_surjective c
 obtain ⟨N,hN⟩:=Aa U V hU hV hUV c
 refine ⟨N,fun n hn=>?_⟩
 rw [XO,L₂,L₂,<- Submodule.map_sup]
 exact ⟨_,hN n hn,rfl⟩
theorem XQ (U:Set X):L₁ U <= (L₁ U).comap k3:=by
 intro c hc
 rw [<- u9] at hc
 obtain ⟨c,rfl⟩:=hc
 change k3 (c3 (inc U) c) ∈ L₁ U
 rw [Pw,<- u9]
 exact ⟨k3 c,rfl⟩
theorem XR (U:Set X):L₂ U <= (L₂ U).comap j4:=by
 intro c hc
 rw [<- o4] at hc
 obtain ⟨c,rfl⟩:=hc
 change j4 (e9 (inc U) c) ∈ L₂ U
 rw [Xr,<- o4]
 exact ⟨j4 c,rfl⟩
theorem P8 (U:Set X) {c:N₁ X} (hc:c ∈ L₁ U) (n:ℕ):(k3^[n]) c ∈ L₁ U:=by
 induction n with
 | zero=>exact hc
 | succ n ih=>rw [Function.iterate_succ_apply']; exact XQ U ih
theorem P9 (U:Set X) {c:N₂ X} (hc:c ∈ L₂ U) (n:ℕ):(j4^[n]) c ∈ L₂ U:=by
 induction n with
 | zero=>exact hc
 | succ n ih=>rw [Function.iterate_succ_apply']; exact XR U ih
theorem Qa (c:N₂ X) (n:ℕ):d₂ ((j4^[n]) c)=(k3^[n]) (d₂ c):=by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [Function.iterate_succ_apply',Xp,ih]
theorem XS (c:C₃ X) (n:ℕ):d₃ ((S₃^[n]) c)=(j4^[n]) (d₃ c):=by
 induction n with
 | zero=>rfl
 | succ n ih=>simp only [Function.iterate_succ_apply',Xq,ih]
def K₁:ℕ -> N₁ X →ₗ[ℤ] N₂ X
 | 0=>0
 | n+1=>H₁.comp (k3 ^ n) + K₁ n
theorem w7 (n:ℕ) (c:N₁ X):d₂ (K₁ n c)=(k3^[n]) c - c:=by
 induction n with
 | zero=>simp [K₁]
 | succ n ih=>
  simp only [K₁,LinearMap.add_apply,LinearMap.comp_apply,map_add,yD,ih]
  rw [Module.End.pow_apply,Function.iterate_succ_apply']
  abel
theorem Qb (U:Set X) {c:N₁ X} (hc:c ∈ L₁ U) (n:ℕ):K₁ n c ∈ L₂ U:=by
 induction n with
 | zero=>exact Submodule.zero_mem _
 | succ n ih=>
  change H₁ ((k3 ^ n) c) + K₁ n c ∈ L₂ U
  rw [Module.End.pow_apply]
  exact Submodule.add_mem _ (XH U (P8 U hc n)) ih
end EilenbergGanea.CubicalSingular
end
noncomputable section
open Classical Set Topology
namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X:Type*} [TopologicalSpace X] {G:Type*} [Group G]
structure Local (U:Set (Set X)) where
 value:a5 X -> G
 constant:∀ x,value (ContinuousMap.const I x)=1
 split:∀ γ ∈ CubicalMesh.small U,value γ=value (jG γ false) * value (jG γ true)
 bx8:∀ σ ∈ CubicalMesh.small U,
  value (e4 σ 0) * value (eW σ 1)=value (eW σ 0) * value (e4 σ 1)
namespace Local
variable {U:Set (Set X)} (l:Local (G:=G) U)
def fold:ℕ -> a5 X -> G
 | 0,γ=>l.value γ
 | n+1,γ=>fold n (jG γ false) * fold n (jG γ true)
def pO (n:ℕ) (γ:a5 X):Prop:=
 CubicalMesh.Dx half U n γ
def Mr (n:ℕ) (σ:c4 X):Prop:=
 CubicalMesh.Dx r9 U n σ
omit [Group G] in
theorem Mt {D E:Type*} [MetricSpace D] [MetricSpace E]
  {γ:C(D,X)} (h:γ ∈ CubicalMesh.small U) (f:C(E,D)) :
  γ.comp f ∈ CubicalMesh.small U:=by
 obtain ⟨u,hu,hγ⟩:=h
 refine ⟨u,hu,?_⟩
 rintro y ⟨x,hx⟩
 exact hx ▸ hγ ⟨f x,rfl⟩
theorem Qc {γ:a5 X} (h:γ ∈ CubicalMesh.small U) (n:ℕ) :
  l.fold n γ=l.value γ:=by
 induction n generalizing γ with
 | zero=>rfl
 | succ n ih=>
  change l.fold n (jG γ false) * l.fold n (jG γ true)=_
  rw [ih (γ:=jG γ false) (Mt h _),ih (γ:=jG γ true) (Mt h _),<- l.split γ h]
theorem Cj {n:ℕ} {γ:a5 X} (h:pO (U:=U) n γ) (m:ℕ) (hm:n <= m) :
  l.fold m γ=l.fold n γ:=by
 induction n generalizing m γ with
 | zero=>exact l.Qc h m
 | succ n ih=>
  obtain ⟨k,rfl⟩:=Nat.exists_eq_succ_of_ne_zero (by omega:m ≠ 0)
  change l.fold k (jG γ false) * l.fold k (jG γ true)=_
  rw [ih (show pO (U:=U) n (jG γ false) from h false) k (by omega),ih (show pO (U:=U) n (jG γ true) from h true) k (by omega)]
  rfl
variable (hU:∀ u ∈ U,IsOpen u) (hcover:⋃₀ U=univ)
include hU hcover
omit [Group G] in
theorem i8 (γ:a5 X):∀ᶠ n in Filter.atTop,pO (U:=U) n γ:=by
 exact CubicalMesh.uW half (by norm_num) (by norm_num:(1/2:ℝ)<1)
  (fun b x y=>(Mj b x y).le) g7 U hU hcover γ (fun _ h=>h) (fun _ _ h=>h)
omit [Group G] in
theorem XT (σ:c4 X):∀ᶠ n in Filter.atTop,Mr (U:=U) n σ:=by
 exact CubicalMesh.uW r9 (by norm_num) (by norm_num:(1/2:ℝ)<1)
  Ml (fun x y=>max_le (g7 _ _) (g7 _ _)) U hU hcover σ (fun _ h=>h) (fun _ _ h=>h)
def depth (γ:a5 X):ℕ:=((i8 hU hcover γ).exists).choose
theorem Qd (γ:a5 X):pO (U:=U) (depth hU hcover γ) γ:=
 ((i8 hU hcover γ).exists).choose_spec
def transport (γ:a5 X):G:=l.fold (depth hU hcover γ) γ
theorem j1 {n:ℕ} {γ:a5 X} (h:pO (U:=U) n γ) :
  l.transport hU hcover γ=l.fold n γ:=by
 let m:=max n (depth hU hcover γ)
 exact (l.Cj (Qd hU hcover γ) m (le_max_right _ _)).symm.trans
  (l.Cj h m (le_max_left _ _))
theorem Qe {γ:a5 X} (h:γ ∈ CubicalMesh.small U) :
  l.transport hU hcover γ=l.value γ:=l.Qc h _
theorem KR (x:X):l.transport hU hcover (ContinuousMap.const I x)=1:=by
 rw [l.Qe hU hcover,l.constant]
 have hx:x ∈ ⋃₀ U:=hcover ▸ mem_univ x
 obtain ⟨u,hu,hx⟩:=hx
 refine ⟨u,hu,?_⟩
 rintro y ⟨t,rfl⟩
 exact hx
omit hU hcover in
theorem XZ (A B C D E F H K M₀ M₁ N₀ N₁:G)
  (h₀:A*M₀=C*N₀) (h₁:B*D=M₀*N₁)
  (h₂:N₀*M₁=E*F) (h₃:N₁*H=M₁*K) :
  (A*B)*(D*H)=(C*E)*(F*K):=by
 calc
  _=A*((B*D)*H):=by simp only [mul_assoc]
  _=A*((M₀*N₁)*H):=by rw [h₁]
  _=(A*M₀)*(N₁*H):=by simp only [mul_assoc]
  _=(C*N₀)*(M₁*K):=by rw [h₀,h₃]
  _=C*((N₀*M₁)*K):=by simp only [mul_assoc]
  _=C*((E*F)*K):=by rw [h₂]
  _=(C*E)*(F*K):=by simp only [mul_assoc]
omit hU hcover in
theorem X0 {n:ℕ} {σ:c4 X} (h:Mr (U:=U) n σ) :
  l.fold n (e4 σ 0) * l.fold n (eW σ 1) =
   l.fold n (eW σ 0) * l.fold n (e4 σ 1):=by
 induction n generalizing σ with
 | zero=>exact l.bx8 σ h
 | succ n ih=>
  have h₀:=ih (σ:=v7 σ false false) (h (false,false))
  have h₁:=ih (σ:=v7 σ true false) (h (true,false))
  have h₂:=ih (σ:=v7 σ false true) (h (false,true))
  have h₃:=ih (σ:=v7 σ true true) (h (true,true))
  simp only [Ph,Pk,j3,m4,EU] at h₀ h₁ h₂ h₃
  exact XZ _ _ _ _ _ _ _ _ _ _ _ _ h₀ h₁ h₂ h₃
omit hU hcover [Group G] in
theorem DX {n:ℕ} {σ:c4 X} (h:Mr (U:=U) n σ) (f:C(I,I × I))
  (comm:∀ b,∃ i,f.comp (half b) = (r9 i).comp f):pO (U:=U) n (σ.comp f):=by
 induction n generalizing σ with
 | zero=>exact Mt h f
 | succ n ih=>
  intro b
  obtain ⟨i,hi⟩:=comm b
  change pO (U:=U) n (σ.comp (f.comp (half b)))
  rw [hi]
  exact ih (σ:=σ.comp (r9 i)) (h i)
theorem Yb (σ:c4 X) :
    l.transport hU hcover (e4 σ 0) * l.transport hU hcover (eW σ 1) =
      l.transport hU hcover (eW σ 0) * l.transport hU hcover (e4 σ 1):=by
  obtain ⟨n,hσ⟩:=(XT hU hcover σ).exists
  have left (a:I) (i:Bool) (ha:half i a=a):pO (U:=U) n (eW σ a):=by
    apply DX hσ (⟨fun t=>(a,t),by fun_prop⟩:C(I,I × I))
    intro b
    exact ⟨(i,b),ContinuousMap.ext fun _=>Prod.ext ha.symm rfl⟩
  have right (a:I) (i:Bool) (ha:half i a=a):pO (U:=U) n (e4 σ a):=by
    apply DX hσ (⟨fun t=>(t,a),by fun_prop⟩:C(I,I × I))
    intro b
    exact ⟨(b,i),ContinuousMap.ext fun _=>Prod.ext rfl ha.symm⟩
  rw [l.j1 hU hcover (right _ _ j3),l.j1 hU hcover (left _ _ m4),
    l.j1 hU hcover (left _ _ j3),l.j1 hU hcover (right _ _ m4)]
  exact l.X0 hσ
end Local
end EilenbergGanea.PathTransport
namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X:Type*} [TopologicalSpace X] {G:Type*} [Group G]
variable {U:Set (Set X)} (l:Local (G:=G) U)
variable (hU:∀ u ∈ U,IsOpen u) (hcover:⋃₀ U=univ)
theorem Yc (γ:a5 X) :
  l.transport hU hcover γ=l.transport hU hcover (jG γ false) * l.transport hU hcover (jG γ true):=by
 obtain ⟨n,h₀,h₁⟩:=((i8 hU hcover (jG γ false)).and (i8 hU hcover (jG γ true))).exists
 have hγ:pO (U:=U) (n+1) γ:=by rintro (_|_) <;> assumption
 rw [l.j1 hU hcover hγ,l.j1 hU hcover h₀,l.j1 hU hcover h₁]
 rfl
omit [Group G] in
theorem Qg {x y z:X} (p:Path x y) (q:Path y z) :
  jG (p.trans q).toContinuousMap false=p.toContinuousMap:=by
 apply ContinuousMap.ext
 intro t
 change (p.trans q) (half false t)=p t
 rw [<- Path.extend_extends' (p.trans q),Path.extend_trans_of_le_half]
 ·have h:2 * (half false t:ℝ)=(t:ℝ):=by simp [half]; ring
  rw [h,Path.extend_extends']
 ·change (t:ℝ)/2 <= 1/2
  linarith [t.property.2]
omit [Group G] in
theorem Qj {x y z:X} (p:Path x y) (q:Path y z) :
  jG (p.trans q).toContinuousMap true=q.toContinuousMap:=by
 apply ContinuousMap.ext
 intro t
 change (p.trans q) (half true t)=q t
 rw [<- Path.extend_extends' (p.trans q),Path.extend_trans_of_half_le]
 ·have h:2 * (half true t:ℝ) - 1=(t:ℝ):=by simp [half]; ring
  rw [h,Path.extend_extends']
 ·change 1/2 <= (1+(t:ℝ))/2
  linarith [t.property.1]
theorem Yd {x y z:X} (p:Path x y) (q:Path y z) :
  l.transport hU hcover (p.trans q).toContinuousMap =
   l.transport hU hcover p.toContinuousMap * l.transport hU hcover q.toContinuousMap:=by
 rw [l.Yc,Qg,Qj]
theorem Qk {x y:X} {p q:Path x y} (H:p.Homotopy q) :
  l.transport hU hcover p.toContinuousMap=l.transport hU hcover q.toContinuousMap:=by
 have h:=l.Yb hU hcover H.toHomotopy.toContinuousMap
 have e₀:eW H.toHomotopy.toContinuousMap 0=p.toContinuousMap:=by ext t; simp [eW]
 have e₁:eW H.toHomotopy.toContinuousMap 1=q.toContinuousMap:=by ext t; simp [eW]
 have c₀:e4 H.toHomotopy.toContinuousMap 0=ContinuousMap.const I x:=by ext t; simp [e4]
 have c₁:e4 H.toHomotopy.toContinuousMap 1=ContinuousMap.const I y:=by ext t; simp [e4]
 rw [e₀,e₁,c₀,c₁,l.KR,l.KR,one_mul,mul_one] at h
 exact h.symm
def kA {x y:X}:Path.Homotopic.Quotient x y -> G:=
 Quotient.lift (fun p=>l.transport hU hcover p.toContinuousMap)
  (fun _ _ ⟨H⟩=>l.Qk hU hcover H)
@[simp] theorem dl9 {x y:X} (p:Path x y) :
  l.kA hU hcover (⟦p⟧:Path.Homotopic.Quotient x y) =
   l.transport hU hcover p.toContinuousMap:=rfl
@[simp] theorem Yf (x:X) :
  l.kA hU hcover (Path.Homotopic.Quotient.refl x)=1:=l.KR hU hcover x
@[simp] theorem Yh {x y z:X}
  (p:Path.Homotopic.Quotient x y) (q:Path.Homotopic.Quotient y z) :
  l.kA hU hcover (p.trans q) =
   l.kA hU hcover p * l.kA hU hcover q:=by
 induction p using Quotient.inductionOn
 induction q using Quotient.inductionOn
 exact l.Yd hU hcover _ _
def Dz (x:X):FundamentalGroup X x →* Gᵐᵒᵖ where
 toFun q:=MulOpposite.op (l.kA hU hcover q)
 map_one':=congrArg MulOpposite.op (l.Yf hU hcover x)
 map_mul' p q:=by
  rw [FundamentalGroup.mul_def,l.Yh,MulOpposite.op_mul]
end EilenbergGanea.PathTransport.Local
namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X:Type*} [TopologicalSpace X]
local instance:ContractibleSpace I:=(convex_Icc (0:ℝ) 1).contractibleSpace ⟨0,by norm_num⟩
abbrev PQ (x y:X):=Path.Homotopic.Quotient x y
def kV (γ:a5 X):Path (γ 0) (γ 1):=⟨γ,rfl,rfl⟩
abbrev bR {x y:X} (p:Path x y):PQ x y:=Path.Homotopic.Quotient.mk p
def based {r:X} (q:∀ x,Path r x) {x y:X} (p:PQ x y):(FundamentalGroup X r)ᵐᵒᵖ:=
 MulOpposite.op (((bR (q x)).trans p).trans (bR (q y)).symm)
theorem Ql {r x y z:X} (q:∀ x,Path r x) (p:PQ x y) (s:PQ y z) :
    based q (p.trans s)=based q p * based q s:=by
  apply MulOpposite.unop_injective
  change ((bR (q x)).trans (p.trans s)).trans _ =
    (((bR (q x)).trans p).trans (bR (q y)).symm).trans
      (((bR (q y)).trans s).trans (bR (q z)).symm)
  simp only [Path.Homotopic.Quotient.trans_assoc]
  rw [<- Path.Homotopic.Quotient.trans_assoc (bR (q y)).symm (bR (q y)),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]
@[simp] theorem Qm {r:X} (q:∀ x,Path r x) (x:X) :
  based q (Path.Homotopic.Quotient.refl x)=1:=by
 apply MulOpposite.unop_injective
 change ((bR (q x)).trans (Path.Homotopic.Quotient.refl x)).trans (bR (q x)).symm=_
 simp only [Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.trans_symm]
 rfl
def c0 {r:X} (q:∀ x,Path r x) {x y:X} (p:Path x y):(FundamentalGroup X r)ᵐᵒᵖ:=
 based q (bR p)
theorem f3 {r x y x' y':X} (q:∀ x,Path r x) (p:Path x y) (p':Path x' y')
  (h:∀ t,p t=p' t):c0 q p=c0 q p':=by
 have hx:x=x':=by simpa using h 0
 have hy:y=y':=by simpa using h 1
 subst x'; subst y'
 have hp:p=p':=Path.ext (funext h)
 rw [hp]
theorem s3 {r x y:X} (q:∀ x,Path r x) {p p':Path x y}
  (h:Path.Homotopic p p'):c0 q p=c0 q p':=
 congrArg (based q) (Quotient.sound h)
@[simp] theorem l4 {r x y z:X} (q:∀ x,Path r x) (p:Path x y) (s:Path y z) :
  c0 q (p.trans s)=c0 q p * c0 q s:=by
 exact (congrArg (based q) (Path.Homotopic.Quotient.mk_trans p s)).trans (Ql q _ _)
@[simp] theorem Qn {r:X} (q:∀ x,Path r x) (x:X):c0 q (Path.refl x)=1:=Qm q x
def g2 {r:X} (q:∀ x,Path r x) (γ:a5 X):(FundamentalGroup X r)ᵐᵒᵖ:=
 c0 q (kV γ)
@[simp] theorem u2 {r x y:X} (q:∀ x,Path r x) (p:Path x y) :
  g2 q p.toContinuousMap=c0 q p:=f3 q _ _ (fun _=>rfl)
@[simp] theorem Yj {r:X} (q:∀ x,Path r x) (x:X) :
  g2 q (ContinuousMap.const I x)=1:=Qn q x
def Mv:Path (0:I) (half true 0):=⟨half false,j3,EU⟩
def Bc:Path (half true 0) (1:I):=⟨half true,rfl,m4⟩
theorem Yk {r:X} (q:∀ x,Path r x) (γ:a5 X) :
  g2 q γ=g2 q (jG γ false) * g2 q (jG γ true):=by
 have hp:=(SimplyConnectedSpace.paths_homotopic Path.id (Mv.trans Bc)).map γ
 have h:=s3 q hp
 rw [Path.map_trans,l4] at h
 calc
  g2 q γ=c0 q (Path.id.map γ.continuous):=f3 q _ _ (fun _=>rfl)
  _=c0 q (Mv.map γ.continuous) * c0 q (Bc.map γ.continuous):=h
  _=_:=congrArg₂ (· * ·)
   (f3 q (Mv.map γ.continuous) (kV (jG γ false)) (fun _=>rfl))
   (f3 q (Bc.map γ.continuous) (kV (jG γ true)) (fun _=>rfl))
def Mw:Path ((0:I),(0:I)) (1,0):=Path.id.prod (Path.refl 0)
def Mz:Path ((1:I),(0:I)) (1,1):=(Path.refl 1).prod Path.id
def MA:Path ((0:I),(0:I)) (0,1):=(Path.refl 0).prod Path.id
def ME:Path ((0:I),(1:I)) (1,1):=Path.id.prod (Path.refl 1)
theorem Yl (σ:c4 X) :
  Path.Homotopic ((Mw.map σ.continuous).trans (Mz.map σ.continuous))
   ((MA.map σ.continuous).trans (ME.map σ.continuous)):=by
 have h:=(SimplyConnectedSpace.paths_homotopic (Mw.trans Mz) (MA.trans ME)).map σ
 simpa only [Path.map_trans] using h
theorem Qo {r:X} (q:∀ x,Path r x) (σ:c4 X) :
  g2 q (e4 σ 0) * g2 q (eW σ 1) =
   g2 q (eW σ 0) * g2 q (e4 σ 1):=by
 have h:=s3 q (Yl σ)
 rw [l4,l4] at h
 have h₀:=f3 q (Mw.map σ.continuous) (kV (e4 σ 0)) (fun _=>rfl)
 have h₁:=f3 q (Mz.map σ.continuous) (kV (eW σ 1)) (fun _=>rfl)
 have h₂:=f3 q (MA.map σ.continuous) (kV (eW σ 0)) (fun _=>rfl)
 have h₃:=f3 q (ME.map σ.continuous) (kV (e4 σ 1)) (fun _=>rfl)
 exact (congrArg₂ (· * ·) h₀ h₁).symm.trans (h.trans (congrArg₂ (· * ·) h₂ h₃))
end EilenbergGanea.PathTransport
namespace EilenbergGanea.CubicalSingular
variable {X:Type*} [TopologicalSpace X]
theorem wJ [ContractibleSpace X]
  (U V:Set X) (hU:IsOpen U) (hV:IsOpen V) (hUV:U ∪ V=univ)
  {z:N₁ X} (hz:z ∈ L₁ (U ∩ V))
  {a b:N₂ X} (ha:a ∈ L₂ U) (hb:b ∈ L₂ V) (hda:d₂ a=z) (hdb:d₂ b=z) :
  ∃ c ∈ L₂ (U ∩ V),d₂ c=z:=by
 have hcycle:d₂ (a-b)=0:=by rw [map_sub,hda,hdb,sub_self]
 obtain ⟨w,hw⟩:=r7 (a-b) hcycle
 obtain ⟨n,hn⟩:=Ac U V hU hV hUV w
 obtain ⟨u,hu,v,hv,huv⟩:=Submodule.mem_sup.mp (hn n le_rfl)
 have he:d₃ u + d₃ v=(j4^[n]) a - (j4^[n]) b:=by
  rw [<- map_add,huv,XS,hw,<- Module.End.pow_apply]
  simpa only [Module.End.pow_apply] using (j4 ^ n).map_sub a b
 let c:N₂ X:=(j4^[n]) a - d₃ u
 have hcU:c ∈ L₂ U:=Submodule.sub_mem _ (P9 U ha n) (P7 U hu)
 have hc_eq:c=(j4^[n]) b + d₃ v:=by
  apply sub_eq_iff_eq_add.mpr
  calc
   (j4^[n]) a=((j4^[n]) a - (j4^[n]) b) + (j4^[n]) b:=(sub_add_cancel _ _).symm
   _=(d₃ u + d₃ v) + (j4^[n]) b:=by rw [he]
   _=((j4^[n]) b + d₃ v) + d₃ u:=by abel
 have hcV:c ∈ L₂ V:=by
  rw [hc_eq]
  exact Submodule.add_mem _ (P9 V hb n) (P7 V hv)
 have hdc:d₂ c=(k3^[n]) z:=by
  change d₂ ((j4^[n]) a - d₃ u)=_
  rw [map_sub,Qa,hda,WX,sub_zero]
 refine ⟨c - K₁ n z,?_,?_⟩
 ·exact Submodule.sub_mem _ (by rw [Xz]; exact ⟨hcU,hcV⟩) (Qb _ hz n)
 ·rw [map_sub,hdc,w7]
  abel
theorem v8 [ContractibleSpace X]
  (U V:Set X) (hU:IsOpen U) (hV:IsOpen V) (hUV:U ∪ V=univ)
  {z:N₁ X} (hzU:z ∈ L₁ U) (hz:d₁ z=0) :
  ∃ t ∈ L₁ (U ∩ V),d₁ t=0 /\
   (∃ b ∈ L₂ U,d₂ b=t-z) /\ (∃ b ∈ L₂ V,d₂ b=t):=by
 obtain ⟨a,ha⟩:=r0 z hz
 obtain ⟨n,hn⟩:=XP U V hU hV hUV a
 obtain ⟨u,hu,v,hv,huv⟩:=Submodule.mem_sup.mp (hn n le_rfl)
 have he:d₂ u + d₂ v=(k3^[n]) z:=by rw [<- map_add,huv,Qa,ha]
 have ht_eq:d₂ v=(k3^[n]) z - d₂ u:=by
  apply eq_sub_iff_add_eq.mpr
  rw [add_comm,he]
 refine ⟨d₂ v,?_,O6 v,?_,⟨v,hv,rfl⟩⟩
 ·rw [dm1]
  refine ⟨?_,PW V hv⟩
  rw [ht_eq]
  exact Submodule.sub_mem _ (P8 U hzU n) (PW U hu)
 ·refine ⟨K₁ n z-u,Submodule.sub_mem _ (Qb U hzU n) hu,?_⟩
  rw [map_sub,w7,ht_eq]
  abel
def l5 (U:Set X):Submodule ℤ (N₁ X):=L₁ U ⊓ LinearMap.ker d₁
def Ym (U:Set X):Submodule ℤ (N₁ X):=(L₂ U).map d₂
def boundaries (U:Set X):Submodule ℤ (l5 U):=(Ym U).comap (l5 U).subtype
abbrev n8 (U:Set X):=l5 U ⧸ boundaries U
end EilenbergGanea.CubicalSingular
namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y Z:Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
theorem E0 {D:Type*} [TopologicalSpace D] (f:C(X,Y)) {U:Set X} {V:Set Y}
  (hf:MapsTo f U V):(Finsupp.supported ℤ ℤ (jV D U)).map
  (Finsupp.lmapDomain ℤ ℤ (fun σ=>f.comp σ)) ≤ Finsupp.supported ℤ ℤ (jV D V):=by
 rw [Finsupp.lmapDomain_supported]
 apply Finsupp.supported_mono
 rintro _ ⟨σ,hσ,rfl⟩ _ ⟨t,rfl⟩
 exact hf (hσ ⟨t,rfl⟩)
theorem Yn (f:C(X,Y)) {U:Set X} {V:Set Y} (hf:MapsTo f U V) :
  L₁ U <= (L₁ V).comap (c3 f):=by
 rw [← Submodule.map_le_iff_le_comap,L₁,← Submodule.map_comp,c3,Submodule.mapQ_mkQ,Submodule.map_comp]
 exact Submodule.map_mono (E0 f hf)
theorem Yo (f:C(X,Y)) {U:Set X} {V:Set Y} (hf:MapsTo f U V) :
  L₂ U <= (L₂ V).comap (e9 f):=by
 rw [← Submodule.map_le_iff_le_comap,L₂,← Submodule.map_comp,e9,Submodule.mapQ_mkQ,Submodule.map_comp]
 exact Submodule.map_mono (E0 f hf)
@[simp] theorem Gk:L₁ (univ:Set X)=⊤:=by
 rw [L₁,IU,Pz,Finsupp.supported_univ,Submodule.map_top]
 exact LinearMap.range_eq_top.mpr (D₁ X).mkQ_surjective
@[simp] theorem KV:L₂ (univ:Set X)=⊤:=by
 rw [L₂,Dw,Pz,Finsupp.supported_univ,Submodule.map_top]
 exact LinearMap.range_eq_top.mpr (D₂ X).mkQ_surjective
def qB (f:C(X,Y)) {U:Set X} {V:Set Y} (hf:MapsTo f U V) :
  l5 U →ₗ[ℤ] l5 V:=
 (c3 f).restrict (fun z hz=>⟨Yn f hf hz.1,by
  change d₁ (c3 f z)=0
  rw [Md,hz.2,map_zero]⟩)
theorem Qr (f:C(X,Y)) {U:Set X} {V:Set Y} (hf:MapsTo f U V) :
  boundaries U <= (boundaries V).comap (qB f hf):=by
 rintro z ⟨b,hb,he⟩
 refine ⟨e9 f b,Yo f hf hb,?_⟩
 exact (Gd f b).trans (congrArg (c3 f) he)
def homologyMap (f:C(X,Y)) {U:Set X} {V:Set Y} (hf:MapsTo f U V) :
  n8 U →ₗ[ℤ] n8 V:=
 (boundaries U).mapQ (boundaries V) (qB f hf) (Qr f hf)
@[simp] theorem y2 (f:C(X,Y)) {U:Set X} {V:Set Y} (hf:MapsTo f U V)
  (z:l5 U):homologyMap f hf ((boundaries U).mkQ z) =
   (boundaries V).mkQ (qB f hf z):=rfl
theorem homologyMap_id (U:Set X):homologyMap (ContinuousMap.id X) (show MapsTo (ContinuousMap.id X) U U from fun _ h=>h)=LinearMap.id:=by
 apply LinearMap.ext
 intro q
 obtain ⟨z,rfl⟩:=(boundaries U).mkQ_surjective q
 rw [y2,LinearMap.id_apply]
 congr 1
 apply Subtype.ext
 exact O9 z.val
theorem homologyMap_comp (g:C(Y,Z)) (f:C(X,Y)) {U:Set X} {V:Set Y} {W:Set Z}
  (hf:MapsTo f U V) (hg:MapsTo g V W) :
  homologyMap (g.comp f) (hg.comp hf)=(homologyMap g hg).comp (homologyMap f hf):=by
 apply LinearMap.ext
 intro q
 obtain ⟨z,rfl⟩:=(boundaries U).mkQ_surjective q
 simp only [y2,LinearMap.comp_apply]
 congr 1
 apply Subtype.ext
 exact Me g f z.val
abbrev d0 (X:Type*) [TopologicalSpace X]:=n8 (univ:Set X)
def gG (f:C(X,Y)):d0 X →ₗ[ℤ] d0 Y:=homologyMap f (mapsTo_univ _ _)
@[simp] theorem bh1:gG (ContinuousMap.id X)=LinearMap.id:=homologyMap_id univ
@[simp] theorem m9 (g:C(Y,Z)) (f:C(X,Y)) :
  gG (g.comp f)=(gG g).comp (gG f):=homologyMap_comp g f _ _
def Cv (e:X ≃ₜ Y):d0 X ≃ₗ[ℤ] d0 Y:=
 LinearEquiv.ofLinearMap (gG (e:C(X,Y))) (gG (e.symm:C(Y,X)))
  (by rw [← m9]; simp) (by rw [← m9]; simp)
end EilenbergGanea.CubicalSingular
namespace EilenbergGanea.CubicalSingular
open Set PathTransport
variable {X:Type*} [TopologicalSpace X]
theorem bY {x y:X} (p:Path x y):d₁ (gen₁ p.toContinuousMap)=
  Finsupp.single y 1 - Finsupp.single x 1:=by
 simp only [gen₁,O5,KI,one_smul]
 change Finsupp.single (p 1) _ - Finsupp.single (p 0) _=_
 rw [p.target,p.source]
def anchors {r:X} (q:∀ x,Path r x):C₀ X →ₗ[ℤ] N₁ X:=
 Finsupp.linearCombination ℤ (fun x=>gen₁ (q x).toContinuousMap)
variable {r:X} (q:∀ x,Path r x)
def oW:N₁ X →ₗ[ℤ] l5 (univ:Set X):=
  (LinearMap.id - (anchors q).comp d₁).codRestrict _ (by
    intro z
    refine ⟨by rw [Gk]; trivial,?_⟩
    change d₁ (z - anchors q (d₁ z))=0
    obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective z
    have he:(d₁.comp (anchors q)).comp b₁=b₁:=by
      apply Finsupp.lhom_ext
      intro γ m
      simp only [LinearMap.comp_apply,KI,map_smul,map_sub,anchors,
        Finsupp.linearCombination_single,one_smul,bY]
      congr 1 <;> abel
    rw [map_sub]
    exact sub_eq_zero.mpr (LinearMap.congr_fun he c).symm
  )
def g6:N₁ X →ₗ[ℤ] d0 X:=(boundaries univ).mkQ.comp (oW q)
theorem zG (z:l5 (univ:Set X)):g6 q z.val=(boundaries univ).mkQ z:=by
 apply congrArg (boundaries univ).mkQ
 apply Subtype.ext
 change z.val - anchors q (d₁ z.val)=z.val
 rw [z.property.2,map_zero,sub_zero]
@[simp] theorem Qt (b:N₂ X):g6 q (d₂ b)=0:=by
 let z:l5 (univ:Set X):=⟨d₂ b,by rw [Gk]; trivial,O6 b⟩
 rw [show d₂ b=z.val from rfl,zG]
 exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨b,by rw [KV]; trivial,rfl⟩
def gR {x y:X} (p:Path x y):d0 X:=g6 q (gen₁ p.toContinuousMap)
@[simp] theorem Qv (x:X):gen₁ (ContinuousMap.const I x)=0:=
 (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.subset_span ⟨x,rfl⟩)
@[simp] theorem Yp (x:X):gR q (Path.refl x)=0:=by
 change g6 q (gen₁ (ContinuousMap.const I x))=0
 rw [Qv,map_zero]
theorem Yq (z:N₁ X):g6 q (k3 z)=g6 q z:=by
 have h:=Qt q (K₁ 1 z)
 rw [w7] at h
 exact sub_eq_zero.mp (by simpa only [Function.iterate_one,map_sub] using h)
theorem Yr {x y z:X} (p:Path x y) (v:Path y z) :
    gR q (p.trans v)=gR q p + gR q v:=by
  rw [gR,<- Yq]
  simp only [gen₁,Xn,Pd,Fintype.sum_bool,map_add,
    PathTransport.Local.Qg,PathTransport.Local.Qj]
  rw [add_comm]
  rfl
theorem Yt {x y:X} {p v:Path x y} (H:p.Homotopy v) :
  gR q p=gR q v:=by
 have h:=Qt q (gen₂ H.toHomotopy.toContinuousMap)
 have e₀:eW H.toHomotopy.toContinuousMap 0=p.toContinuousMap:=by ext t; simp [eW]
 have e₁:eW H.toHomotopy.toContinuousMap 1=v.toContinuousMap:=by ext t; simp [eW]
 have c₀:e4 H.toHomotopy.toContinuousMap 0=ContinuousMap.const I x:=by ext t; simp [e4]
 have c₁:e4 H.toHomotopy.toContinuousMap 1=ContinuousMap.const I y:=by ext t; simp [e4]
 change g6 q ((D₁ X).mkQ (b₂ (Finsupp.single H.toHomotopy.toContinuousMap 1)))=0 at h
 simp only [Jy,one_smul,map_sub,map_add,e₀,e₁,c₀,c₁] at h
 change gR q v - gR q p - g6 q (gen₁ (ContinuousMap.const I y)) +
  g6 q (gen₁ (ContinuousMap.const I x))=0 at h
 have hh:gR q v - gR q p=0:=by simpa only [Qv,map_zero,sub_zero,add_zero] using h
 exact (sub_eq_zero.mp hh).symm
def dO {x y:X}:PQ x y -> d0 X:=
 Quotient.lift (fun p=>gR q p) (fun _ _ ⟨H⟩=>Yt q H)
@[simp] theorem ab1 {x y:X} (p:Path x y) :
  dO q (bR p)=gR q p:=rfl
@[simp] theorem u1 {x y z:X} (p:PQ x y) (v:PQ y z) :
  dO q (p.trans v)=dO q p + dO q v:=by
 induction p using Quotient.inductionOn
 induction v using Quotient.inductionOn
 exact Yr q _ _
@[simp] theorem Qw (x:X):dO q (Path.Homotopic.Quotient.refl x)=0:=
 Yp q x
@[simp] theorem Yv {x y:X} (p:PQ x y) :
  dO q p.symm=-dO q p:=by
 have h:=congrArg (dO q) (Path.Homotopic.Quotient.trans_symm p)
 rw [u1,Qw] at h
 exact eq_neg_of_add_eq_zero_right h
def E3:(FundamentalGroup X r)ᵐᵒᵖ →* Multiplicative (d0 X) where
 toFun g:=Multiplicative.ofAdd (dO q g.unop)
 map_one':=congrArg Multiplicative.ofAdd (Qw q r)
 map_mul' g h:=congrArg Multiplicative.ofAdd (u1 q g.unop h.unop)
abbrev E4 (X:Type*) [TopologicalSpace X] (r:X):=Additive (Abelianization (FundamentalGroup X r)ᵐᵒᵖ)
def m0:E4 X r →ₗ[ℤ] d0 X:=
 (Abelianization.lift (E3 q)).toAdditive.toIntLinearMap
@[simp] theorem bs5 (g:(FundamentalGroup X r)ᵐᵒᵖ) :
  m0 q (Additive.ofMul (Abelianization.of g))=dO q g.unop:=rfl
def f6 {r:X} (q:∀ x,Path r x) (γ:a5 X):E4 X r:=
 Additive.ofMul (Abelianization.of (g2 q γ))
@[simp] theorem ds3 {r:X} (q:∀ x,Path r x) (x:X) :
  f6 q (ContinuousMap.const I x)=0:=by
 simp [f6]
def kW {r:X} (q:∀ x,Path r x):C₁ X →ₗ[ℤ] E4 X r:=
 Finsupp.linearCombination ℤ (f6 q)
def jR {r:X} (q:∀ x,Path r x):N₁ X →ₗ[ℤ] E4 X r:=
 (D₁ X).liftQ (kW q) (by
  apply Submodule.span_le.mpr
  rintro _ ⟨x,rfl⟩
  simp [kW,gQ])
@[simp] theorem Qy {r:X} (q:∀ x,Path r x) (γ:a5 X) :
  jR q (gen₁ γ)=f6 q γ:=by simp [jR,gen₁,kW]
theorem Yw {r:X} (q:∀ x,Path r x) (σ:c4 X) :
  f6 q (e4 σ 0) + f6 q (eW σ 1) =
   f6 q (eW σ 0) + f6 q (e4 σ 1):=by
 have h:=congrArg (fun g=>Additive.ofMul (Abelianization.of g)) (Qo q σ)
 simp only [map_mul] at h
 exact h
theorem w8 {r:X} (q:∀ x,Path r x) :
    (jR q).comp d₂=0:=by
  apply LinearMap.ext
  intro z
  obtain ⟨z,rfl⟩:=(D₂ X).mkQ_surjective z
  have he:(kW q).comp b₂=0:=by
    apply Finsupp.lhom_ext
    intro σ a
    simp only [LinearMap.comp_apply,Jy,map_smul,map_sub,map_add,kW,
      Finsupp.linearCombination_single,one_smul,LinearMap.zero_apply]
    have h:=Yw q σ
    have hz:f6 q (eW σ 1) - f6 q (eW σ 0) -
      f6 q (e4 σ 1) + f6 q (e4 σ 0)=0:=by
      calc
        _=(f6 q (e4 σ 0) + f6 q (eW σ 1)) -
          (f6 q (eW σ 0) + f6 q (e4 σ 1)):=by abel
        _=0:=by rw [h,sub_self]
    rw [hz,smul_zero]
  exact LinearMap.congr_fun he z
@[simp] theorem Yx {r:X} (q:∀ x,Path r x) {x y:X} (p:PQ x y) :
  dO q (based q p).unop=gR q (q x) + dO q p - gR q (q y):=by
 simp only [based,MulOpposite.unop_op,u1,Yv,ab1,sub_eq_add_neg]
theorem E5 (x y:X):gR q (q x)=gR q (q y):=by
 apply congrArg (boundaries univ).mkQ
 apply Subtype.ext
 change gen₁ _ - anchors q (d₁ (gen₁ (q x).toContinuousMap)) =
  gen₁ _ - anchors q (d₁ (gen₁ (q y).toContinuousMap))
 simp only [bY,map_sub,anchors,Finsupp.linearCombination_single,one_smul]
 abel
theorem Yy (z:N₁ X):m0 q (jR q z)=g6 q z:=by
 obtain ⟨c,rfl⟩:=(D₁ X).mkQ_surjective z
 have he:(m0 q).comp (kW q)=(g6 q).comp (D₁ X).mkQ:=by
  apply Finsupp.lhom_ext
  intro γ m
  rw [<- Finsupp.smul_single_one γ m]
  simp only [map_smul,LinearMap.comp_apply,kW,Finsupp.linearCombination_single,one_smul]
  congr 1
  change dO q (based q (bR (kV γ))).unop=gR q (kV γ)
  rw [Yx,ab1,E5 q (γ 0) (γ 1)]
  abel
 exact LinearMap.congr_fun he c
theorem Qz {r:X} (q:∀ x,Path r x) (g:FundamentalGroup X r) :
  Abelianization.of (based q g)=Abelianization.of (MulOpposite.op g):=by
 let u:FundamentalGroup X r:=bR (q r)
 have he:based q g=(MulOpposite.op u:(FundamentalGroup X r)ᵐᵒᵖ) *
   MulOpposite.op g * (MulOpposite.op u)⁻¹:=rfl
 rw [he,map_mul,map_mul,map_inv]
 simp [mul_comm]
def QC {r:X} (q:∀ x,Path r x):d0 X →ₗ[ℤ] E4 X r:=
 (boundaries univ).liftQ ((jR q).comp (l5 univ).subtype) (by
  rintro z ⟨b,_,hb⟩
  change jR q z.val=0
  change d₂ b=z.val at hb
  rw [<- hb]; exact LinearMap.congr_fun (w8 q) b)
def sI {r:X} (q:∀ x,Path r x):d0 X ≃ₗ[ℤ] E4 X r:=
 LinearEquiv.ofLinearMap (QC q) (m0 q) (by
  apply LinearMap.ext
  intro g
  obtain ⟨w,rfl⟩:∃ w:(FundamentalGroup X r)ᵐᵒᵖ,Additive.ofMul (Abelianization.of w)=g:=
   QuotientGroup.mk'_surjective _ g
  induction w using MulOpposite.rec' with | h w=>
   induction w using Quotient.inductionOn with | h p=>
    let z:l5 (univ:Set X):=⟨gen₁ p.toContinuousMap,by rw [Gk]; trivial,by
     change d₁ (gen₁ p.toContinuousMap)=0; rw [bY,sub_self]⟩
    change QC q (g6 q z.val)=_
    rw [zG]
    change jR q (gen₁ p.toContinuousMap)=_
    rw [Qy,f6,u2]; exact congrArg Additive.ofMul (Qz q (bR p))) (by
  apply LinearMap.ext
  intro h
  obtain ⟨z,rfl⟩:=(boundaries univ).mkQ_surjective h
  change m0 q (jR q z.val)=_
  rw [Yy,zG]; rfl)
end EilenbergGanea.CubicalSingular
end
noncomputable section
open Classical Set Metric Topology
namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology
open CWCover
universe u v
variable {X:Type u} [TopologicalSpace X] {J:Type v} {n:ℕ}
structure Attachment (X:Type u) [TopologicalSpace X] (J:Type v) (n:ℕ) where
 lower:Set X
 ck1:IsClosed lower
 l0:J -> C(e8 n,X)
 boundary:∀ j (z:e8 n),‖z.val‖=1 -> l0 j z ∈ lower
 interior:∀ j (z:e8 n),‖z.val‖ < 1 -> l0 j z ∉ lower
 disjoint:∀ j k (z w:e8 n),‖z.val‖ < 1 -> ‖w.val‖ < 1 ->
  l0 j z=l0 k w -> j=k /\ z=w
 quotient:IsQuotientMap (Sum.elim (Subtype.val:lower -> X)
  (fun p:Σ _:J,e8 n=>l0 p.1 p.2))
namespace Attachment
variable (a:Attachment X J n)
abbrev Rep:=a.lower ⊕ (Σ _:J,e8 n)
def q:a.Rep -> X:=Sum.elim Subtype.val (fun p=>a.l0 p.1 p.2)
def coordinate:a.Rep -> ℝ:=Sum.elim (fun _=>1) (fun p=>‖p.2.val‖)
@[simp] theorem wA (z:e8 n):‖z.val‖ <= 1:=by
 simpa only [mem_closedBall,dist_zero_right] using z.property
theorem pQ (p:a.Rep):a.coordinate p ≤ 1:=by
 cases p with
 | inl x=>exact le_rfl
 | inr c=>exact wA c.2
private theorem I7 (p:a.Rep) (h:a.coordinate p = 1):a.q p ∈ a.lower:=by
 cases p with
 | inl x=>exact x.property
 | inr c=>exact a.boundary _ _ h
theorem KX {p r:a.Rep} (hp:a.coordinate p < 1) (h:a.q p=a.q r):p=r:=by
 cases p with
 | inl x=>exact (lt_irrefl (1:ℝ) hp).elim
 | inr c=>
  have hr:a.coordinate r < 1:=by
   refine lt_of_le_of_ne (a.pQ r) fun e=>?_
   exact a.interior c.1 c.2 hp (show a.q (.inr c) ∈ a.lower by rw [h]; exact a.I7 r e)
  cases r with
  | inl x=>exact (lt_irrefl (1:ℝ) hr).elim
  | inr d=>
   obtain ⟨hj,hz⟩:=a.disjoint _ _ _ _ hp hr h
   exact congrArg Sum.inr (Sigma.ext hj (heq_of_eq hz))
theorem QD (p r:a.Rep) (h:a.q p=a.q r):a.coordinate p=a.coordinate r:=by
 rcases (a.pQ p).lt_or_eq with hp|hp
 ·rw [a.KX hp h]
 rcases (a.pQ r).lt_or_eq with hr|hr
 ·rw [a.KX hr h.symm]
 exact hp.trans hr.symm
theorem QE:Continuous a.coordinate:=by
 apply Continuous.sumElim continuous_const
 exact continuous_sigma (fun _=>continuous_norm.comp continuous_subtype_val)
private def projection:C(a.Rep,X):=⟨a.q,a.quotient.continuous⟩
private def DY:C(a.Rep,ℝ):=⟨a.coordinate,a.QE⟩
def radius:C(X,ℝ):=
 (show IsQuotientMap a.projection from a.quotient).lift a.DY (fun {_ _} h=>a.QD _ _ h)
@[simp] theorem KY (p:a.Rep):a.radius (a.q p)=a.coordinate p:=
 DFunLike.congr_fun ((show IsQuotientMap a.projection from a.quotient).lift_comp a.DY (fun {_ _} h=>a.QD _ _ h)) p
@[simp] theorem MJ (x:a.lower):a.radius x.val=1:=a.KY (.inl x)
@[simp] theorem j7 (j:J) (z:e8 n):a.radius (a.l0 j z)=‖z.val‖:=
 a.KY (.inr ⟨j,z⟩)
theorem Yz (x:X):a.radius x=1 ↔ x ∈ a.lower:=by
 constructor
 ·intro h
  obtain ⟨p,rfl⟩:=a.quotient.surjective x
  change a.radius (a.q p)=1 at h
  rw [a.KY] at h
  cases p with
  | inl y=>exact y.property
  | inr p=>exact a.boundary p.1 p.2 h
 ·intro h
  exact a.MJ ⟨x,h⟩
def outer:Set X:={x | 0 < a.radius x}
def inner:Set X:={x | a.radius x < 1}
theorem Gm:IsOpen a.outer:=isOpen_lt continuous_const a.radius.continuous
theorem Gp:IsOpen a.inner:=isOpen_lt a.radius.continuous continuous_const
theorem k7:a.outer ∪ a.inner=univ:=by
 ext x
 simp only [mem_union,mem_univ,iff_true]
 change 0 < a.radius x \/ a.radius x < 1
 by_cases h:0 < a.radius x
 ·exact Or.inl h
 ·exact Or.inr (by linarith)
theorem YA:a.lower ⊆ a.outer:=by
 intro x hx
 change 0 < a.radius x
 rw [(a.Yz x).mpr hx]
 norm_num
end Attachment
end EilenbergGanea.CWCollar
namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
open scoped unitInterval
variable {n:ℕ}
abbrev e6 (n:ℕ):={z:e8 n // 0 < ‖z.val‖}
def sK (t:I) (z:e6 n):ℝ:=(1-t.val) + t.val / ‖z.val.val‖
theorem YB (t:I) (z:e6 n):0 <= sK t z:=
 add_nonneg (sub_nonneg.mpr t.property.2) (div_nonneg t.property.1 (norm_nonneg _))
def lP (t:I) (z:e6 n):Fin n -> ℝ:=sK t z • z.val.val
theorem ML (t:I) (z:e6 n) :
  ‖lP t z‖=(1-t.val)*‖z.val.val‖ + t.val:=by
 rw [lP,norm_smul,Real.norm_eq_abs,abs_of_nonneg (YB t z)]
 dsimp [sK]
 rw [add_mul,div_mul_cancel₀ _ (ne_of_gt z.property)]
theorem YC (t:I) (z:e6 n):0 < ‖lP t z‖:=by
 rw [ML]
 have hz:=z.property
 have hb:=Attachment.wA z.val
 have ht:=mul_nonneg t.property.1 (sub_nonneg.mpr hb)
 nlinarith
theorem YH (t:I) (z:e6 n):‖lP t z‖ <= 1:=by
 rw [ML]
 have h:=mul_nonneg (sub_nonneg.mpr t.property.2) (sub_nonneg.mpr (Attachment.wA z.val))
 nlinarith
def nS (t:I) (z:e6 n):e6 n:=
 ⟨⟨lP t z,by simpa only [mem_closedBall,dist_zero_right] using YH t z⟩,
  YC t z⟩
@[simp] theorem ds4 (z:e6 n):nS 0 z=z:=by
 apply Subtype.ext
 apply Subtype.ext
 simp [nS,lP,sK]
@[simp] theorem YI (z:e6 n):‖(nS 1 z).val.val‖=1:=by
 change ‖lP 1 z‖=1
 rw [ML]
 norm_num
theorem s7 (t:I) (z:e6 n) (hz:‖z.val.val‖=1) :
  nS t z=z:=by
 apply Subtype.ext
 apply Subtype.ext
 change ((1-t.val) + t.val / ‖z.val.val‖) • z.val.val=z.val.val
 rw [hz,div_one,sub_add_cancel,one_smul]
theorem YJ:Continuous (fun p:I × e6 n=>nS p.1 p.2):=by
 apply Continuous.subtype_mk
 apply Continuous.subtype_mk
 change Continuous (fun p:I × e6 n=>
  ((1-p.1.val) + p.1.val / ‖p.2.val.val‖) • p.2.val.val)
 have hz:Continuous (fun p:I × e6 n=>p.2.val.val):=by fun_prop
 exact ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
  ((continuous_subtype_val.comp continuous_fst).div (continuous_norm.comp hz)
   (fun p=>ne_of_gt p.2.property))).smul hz
end EilenbergGanea.CWCollar
namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
open scoped unitInterval
variable {X J:Type*} [TopologicalSpace X] {n:ℕ}
namespace Attachment
variable (a:Attachment X J n)
private def C7 {B T:Type*} [TopologicalSpace B] (P:B → Prop) :
  (Σ _:T,Subtype P) ≃ₜ {s:Σ _:T,B // P s.2}:=by
 let f (s:Σ _:T,Subtype P):{s:Σ _:T,B // P s.2}:=⟨⟨s.1,s.2.val⟩,s.2.property⟩
 have he:IsEmbedding (Sigma.map (β₁:=fun _:T=>Subtype P) (β₂:=fun _:T=>B) id (fun _=>Subtype.val)):=
  (isEmbedding_sigmaMap («σ»:=fun _:T=>Subtype P) (τ:=fun _:T=>B) (f₂:=fun _:T=>@Subtype.val B P) Function.injective_id).2 fun _=>.subtypeVal
 exact (isHomeomorph_iff_isEmbedding_surjective.mpr
  (show IsEmbedding f ∧ Function.Surjective f from
   ⟨he.codRestrict {s:Σ _:T,B | P s.2} (fun s=>s.2.property),fun ⟨⟨i,b⟩,h⟩=>⟨⟨i,⟨b,h⟩⟩,rfl⟩⟩)).homeomorph
private def Kk {B C:Type*} [TopologicalSpace B] [TopologicalSpace C]
    (S:Set (B ⊕ C)) (h:IsOpen S) :
    (Sum.inl ⁻¹' S) ⊕ (Sum.inr ⁻¹' S) ≃ₜ S:=
  Equiv.subtypeSum.symm.toHomeomorphOfContinuousOpen (continuous_sum_dom.2
    ⟨(continuous_inl.comp continuous_subtype_val).subtype_mk _,
     (continuous_inr.comp continuous_subtype_val).subtype_mk _⟩)
    (isOpenMap_sum.2 ⟨(isOpenMap_inl.comp (h.preimage continuous_inl).isOpenMap_subtype_val).subtype_mk _,
      (isOpenMap_inr.comp (h.preimage continuous_inr).isOpenMap_subtype_val).subtype_mk _⟩)
private def Bd (R:Set ℝ) (ho:IsOpen R) :
  {_x:a.lower // (1:ℝ) ∈ R} ⊕ (Σ _:J,{z:e8 n // ‖z.val‖ ∈ R}) ≃ₜ
   a.q ⁻¹' (a.radius ⁻¹' R):=
 ((Homeomorph.refl _).sumCongr (C7 _)).trans <|
  (Kk _ (ho.preimage a.QE)).trans (Homeomorph.setCongr (by ext; simp))
private theorem zW {S:Set X} (h:IsOpen S) {D:Type*} [TopologicalSpace D]
  (e:D ≃ₜ a.q ⁻¹' S):IsQuotientMap (S.restrictPreimage a.q ∘ e):=
 ((show IsQuotientMap a.q from a.quotient).restrictPreimage_isOpen h).comp e.isQuotientMap
abbrev Bh:=a.lower ⊕ (Σ _:J,e6 n)
private def sO:a.Bh ≃ₜ a.q ⁻¹' a.outer:=
 ((show a.lower ≃ₜ {_x:a.lower // (0:ℝ) < 1} from
  ⟨(Equiv.subtypeUnivEquiv (fun _=>zero_lt_one)).symm,continuous_id.subtype_mk _,
   continuous_subtype_val⟩).sumCongr (Homeomorph.refl _)).trans (a.Bd _ isOpen_Ioi)
def lQ:a.Bh → a.outer:=a.outer.restrictPreimage a.q ∘ a.sO
theorem Gq:IsQuotientMap a.lQ:=a.zW a.Gm a.sO
end Attachment
private theorem YM {A B C T:Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace C] [TopologicalSpace T] {f:(A ⊕ B) × T -> C}
  (hA:Continuous (fun p:A × T=>f (.inl p.1,p.2)))
  (hB:Continuous (fun p:B × T=>f (.inr p.1,p.2))):Continuous f:=by
 have h:Continuous (f ∘ (Homeomorph.sumProdDistrib:(A ⊕ B) × T ≃ₜ (A × T) ⊕ (B × T)).symm):=
  continuous_sum_dom.mpr ⟨hA,hB⟩
 simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using h.comp (Homeomorph.sumProdDistrib).continuous
private theorem YN {A:Type*} {B:A -> Type*} {C T:Type*}
  [∀ a,TopologicalSpace (B a)] [TopologicalSpace C] [TopologicalSpace T]
  {f:(Sigma B) × T -> C}
  (h:∀ a,Continuous (fun p:B a × T=>f (⟨a,p.1⟩,p.2))):Continuous f:=by
 have hh:Continuous (f ∘ (Homeomorph.sigmaProdDistrib:(Sigma B) × T ≃ₜ Σ a,B a × T).symm):=
  continuous_sigma h
 simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hh.comp (Homeomorph.sigmaProdDistrib).continuous
namespace Attachment
variable (a:Attachment X J n)
def oX:a.Bh × I -> a.Bh:=fun p=>
 match p.1 with
 | .inl x=>.inl x
 | .inr c=>.inr ⟨c.1,nS p.2 c.2⟩
theorem YO:Continuous a.oX:=by
 apply YM
 ·exact continuous_inl.comp continuous_fst
 ·apply YN
  intro j
  exact continuous_inr.comp (continuous_sigmaMk.comp (YJ.comp continuous_swap))
@[simp] theorem YP (p:a.Bh):a.oX (p,0)=p:=by
 cases p with
 | inl x=>rfl
 | inr c=>simp [oX]
theorem YQ (p:a.Bh):(a.lQ (a.oX (p,1))).val ∈ a.lower:=by
 cases p with
 | inl x=>exact x.property
 | inr c=>exact a.boundary c.1 (nS 1 c.2).val (YI c.2)
private theorem zX (p:a.Bh) (t:I) (h:a.radius (a.lQ p).val=1) :
  a.oX (p,t)=p:=by
 cases p with
 | inl x=>rfl
 | inr c=>
  change a.radius (a.l0 c.1 c.2.val)=1 at h
  rw [a.j7] at h
  simp [oX,s7 t c.2 h]
theorem YS (t:I) {p r:a.Bh} (h:a.lQ p=a.lQ r) :
  a.lQ (a.oX (p,t))=a.lQ (a.oX (r,t)):=by
 by_cases hp:a.radius (a.lQ p).val = 1
 ·rw [a.zX p t hp,a.zX r t (h ▸ hp),h]
 have e:=congrArg Subtype.val h
 have lt:a.coordinate (a.sO p).val < 1:=by
  apply lt_of_le_of_ne (a.pQ _)
  rwa [← a.KY]
 have eq:=a.sO.injective (Subtype.ext (a.KX lt e))
 rw [eq]
end Attachment
end EilenbergGanea.CWCollar
namespace EilenbergGanea.CWCollar.Attachment
open Classical Set Metric Topology
open scoped unitInterval
variable {X J:Type*} [TopologicalSpace X] {n:ℕ} (a:Attachment X J n)
private def rP:C(a.Bh × I,a.outer × I):=
 ⟨Prod.map a.lQ id,a.Gq.continuous.prodMap continuous_id⟩
private theorem Bk:IsQuotientMap a.rP:=by
 refine ⟨IsCoinducing.of_isOpen_preimage_iff_isOpen (fun U=>⟨fun h=>?_,
  fun h=>h.preimage a.rP.continuous⟩),a.Gq.surjective.prodMap Function.surjective_id⟩
 exact isOpen_iff_continuous_mem.2 (a.Gq.continuous_lift_prod_left (isOpen_iff_continuous_mem.1 h))
private def oZ:C(a.Bh × I,a.outer):=⟨_,a.Gq.continuous.comp a.YO⟩
private theorem yF:Function.FactorsThrough a.oZ a.rP:=by
 rintro ⟨p,t⟩ ⟨r,u⟩ h
 obtain ⟨h₁,rfl⟩:=Prod.mk.inj (show (a.lQ p,t) = (a.lQ r,u) from h)
 exact a.YS _ h₁
def Ck:C(a.outer × I,a.outer):=a.Bk.lift a.oZ a.yF
@[simp] theorem MO (p:a.Bh) (t:I):a.Ck (a.lQ p,t)=a.lQ (a.oX (p,t)):=
 DFunLike.congr_fun (a.Bk.lift_comp a.oZ a.yF) (p,t)
@[simp] theorem YU (x:a.outer):a.Ck (x,0)=x:=by
 obtain ⟨p,rfl⟩:=a.Gq.surjective x
 rw [a.MO,a.YP]
theorem YV (x:a.outer):(a.Ck (x,1)).val ∈ a.lower:=by
 obtain ⟨p,rfl⟩:=a.Gq.surjective x
 rw [a.MO]; exact a.YQ p
def lB:C(a.lower,a.outer):=
 ⟨fun x=>⟨x.val,a.YA x.property⟩,continuous_subtype_val.subtype_mk _⟩
def l7:C(a.outer,a.lower):=
 ⟨fun x=>⟨(a.Ck (x,1)).val,a.YV x⟩,
  (continuous_subtype_val.comp (a.Ck.continuous.comp (continuous_id.prodMk continuous_const))).subtype_mk _⟩
@[simp] theorem YZ (x:a.lower) (t:I):a.Ck (a.lB x,t)=a.lB x:=by
 change a.Ck (a.lQ (.inl x),t)=a.lQ (.inl x)
 rw [a.MO]
 rfl
@[simp] theorem QG (x:a.lower):a.l7 (a.lB x)=x:=by
 apply Subtype.ext
 change (a.Ck (a.lB x,1)).val=x.val
 exact congrArg Subtype.val (a.YZ x 1)
def yI:(ContinuousMap.id a.outer).Homotopy (a.lB.comp a.l7) where
 toFun p:=a.Ck (p.2,p.1)
 continuous_toFun:=a.Ck.continuous.comp continuous_swap
 map_zero_left:=a.YU
 map_one_left _:=rfl
end EilenbergGanea.CWCollar.Attachment
namespace EilenbergGanea.CWCollar
open Classical Set Metric Topology CWCover
variable {X J:Type*} [TopologicalSpace X] {n:ℕ}
abbrev p5 (n:ℕ):={z:e8 n // ‖z.val‖ < 1}
namespace Attachment
variable (a:Attachment X J n)
private def Cm:(Σ _:J,p5 n) ≃ₜ a.q ⁻¹' a.inner:=by
 letI:IsEmpty {x:a.lower // (1:ℝ) ∈ Iio (1:ℝ)}:=⟨fun x=>lt_irrefl (1:ℝ) x.property⟩
 exact (Homeomorph.emptySum _ _).symm.trans (a.Bd _ isOpen_Iio)
def j6:(Σ _:J,p5 n) ≃ₜ a.inner:=
 (isHomeomorph_iff_isQuotientMap_injective.mpr ⟨a.zW a.Gp a.Cm,by
  intro p r h
  apply a.Cm.injective
  apply Subtype.ext
  exact a.KX p.2.property (congrArg Subtype.val h)⟩).homeomorph
end Attachment
end EilenbergGanea.CWCollar
namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover
variable {X J:Type*} [TopologicalSpace X] {n:ℕ}
abbrev c7 (n:ℕ):={z:p5 n // 0 < ‖z.val.val‖}
namespace Attachment
variable (a:Attachment X J n)
def zH:{x:a.inner // x.val ∈ a.outer} ≃ₜ (a.outer ∩ a.inner:Set X) where
 toFun x:=⟨x.val.val,x.property,x.val.property⟩
 invFun x:=⟨⟨x.val,x.property.2⟩,x.property.1⟩
 left_inv _:=rfl
 right_inv _:=rfl
 continuous_toFun:=(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
 continuous_invFun:=(continuous_subtype_val.subtype_mk _).subtype_mk _
def cZ:(Σ _:J,c7 n) ≃ₜ (a.outer ∩ a.inner:Set X):=
 (C7 _).trans ((a.j6.subtype (p:=fun p=>0 < ‖p.2.val.val‖)
  (q:=fun x=>x.val ∈ a.outer) (by
   intro p
   change (0 < ‖p.2.val.val‖) ↔ (0 < a.radius (a.l0 p.1 p.2.val))
   rw [a.j7])).trans a.zH)
end Attachment
end EilenbergGanea.CWCollar
namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover
def w9 (n:ℕ):p5 n ≃ₜ ball (0:Fin n -> ℝ) 1 where
 toFun z:=⟨z.val.val,by simpa only [mem_ball,dist_zero_right] using z.property⟩
 invFun z:=⟨⟨z.val,ball_subset_closedBall z.property⟩,by simpa only [mem_ball,dist_zero_right] using z.property⟩
 left_inv _:=rfl
 right_inv _:=rfl
 continuous_toFun:=(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
 continuous_invFun:=(continuous_subtype_val.subtype_mk _).subtype_mk _
def m7 (n:ℕ):(Fin n -> ℝ) ≃ₜ p5 n:=
 Homeomorph.unitBall.trans (w9 n).symm
@[simp] theorem y9 (n:ℕ) :
  (m7 n 0).val.val=0:=Homeomorph.coe_unitBall_apply_zero
def kZ (n:ℕ):({0}ᶜ:Set (Fin n -> ℝ)) ≃ₜ c7 n:=
 (m7 n).subtype (p:=fun x=>x ∈ ({0}ᶜ:Set (Fin n -> ℝ)))
  (q:=fun z=>0 < ‖z.val.val‖) (by
   intro x
   simp only [mem_compl_iff,mem_singleton_iff,norm_pos_iff]
   have he:(m7 n x).val.val=0 ↔ x=0:=by
    constructor
    ·intro h
     apply (m7 n).injective
     apply Subtype.ext
     apply Subtype.ext
     simpa only [y9] using h
    ·rintro rfl; exact y9 n
   exact not_congr he.symm)
instance dj6:PathConnectedSpace (c7 2):=by
 have hr:1 < Module.rank ℝ (Fin 2 -> ℝ):=by simp
 let:PathConnectedSpace ({0}ᶜ:Set (Fin 2 -> ℝ)):=
  isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_compl_singleton_of_one_lt_rank hr 0)
 exact (kZ 2).surjective.pathConnectedSpace (kZ 2).continuous
end EilenbergGanea.CWCollar
namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover CategoryTheory
open scoped ContinuousMap
def kO:(Fin 2 -> ℝ) ≃ₜ ℂ:=
 (Homeomorph.piFinTwo (fun _=>ℝ)).trans Complex.equivRealProdCLM.symm.toHomeomorph
@[simp] theorem QH:kO 0=0:=by
 simp [kO,Homeomorph.piFinTwo]
def qH:({0}ᶜ:Set (Fin 2 -> ℝ)) ≃ₜ ({0}ᶜ:Set ℂ):=
 kO.subtype (p:=fun x=>x ∈ ({0}ᶜ:Set (Fin 2 -> ℝ)))
  (q:=fun z=>z ∈ ({0}ᶜ:Set ℂ)) (by
   intro x
   simp only [mem_compl_iff,mem_singleton_iff]
   constructor
   ·intro hx he
    apply hx
    apply kO.injective
    simpa only [QH] using he
   ·intro hx he
    apply hx
    rw [he,QH])
def xB:sphere (0:ℂ) 1 ≃ₜ Circle:=
 Homeomorph.setCongr rfl
def Y0:c7 2 ≃ₜ Circle × Ioi (0:ℝ):=
 (kZ 2).symm.trans (qH.trans
  ((homeomorphUnitSphereProd ℂ).trans (xB.prodCongr (Homeomorph.refl _))))
instance df5:ContractibleSpace (Ioi (0:ℝ)):=
 (convex_Ioi (0:ℝ)).contractibleSpace ⟨1,by norm_num⟩
noncomputable def tO:c7 2 ≃ₕ Circle:=
 Y0.toHomotopyEquiv.trans
  (((ContinuousMap.HomotopyEquiv.refl Circle).prodCongr (ContractibleSpace.hequiv_unit (Ioi (0:ℝ))).some).trans
   (Homeomorph.prodUnique Circle Unit).toHomotopyEquiv)
noncomputable def lT {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (e:X ≃ₕ Y) (x:X):FundamentalGroup X x ≃* FundamentalGroup Y (e x):=
 MulEquiv.ofBijective (FundamentalGroup.map e.toFun x)
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.homEquiv.bijective
noncomputable def DB:ℤ ≃+ AddSubgroup.zmultiples (2 * Real.pi):=by
  let f:ℤ →+ AddSubgroup.zmultiples (2 * Real.pi):=
    { toFun:=fun n=>⟨n • (2 * Real.pi),AddSubgroup.zsmul_mem_zmultiples _ _⟩
      map_zero':=Subtype.ext (zero_zsmul _)
      map_add':=fun m n=>Subtype.ext (add_zsmul _ _ _) }
  apply AddEquiv.ofBijective f
  constructor
  · intro m n h
    have he:=congrArg Subtype.val h
    change m • (2*Real.pi)=n • (2*Real.pi) at he
    simp only [zsmul_eq_mul] at he
    exact_mod_cast mul_right_cancel₀ (show 2*Real.pi ≠ 0 by positivity) he
  · intro x
    obtain ⟨n,hn⟩:=AddSubgroup.mem_zmultiples_iff.mp x.property
    exact ⟨n,Subtype.ext hn⟩
noncomputable def zK:FundamentalGroup Circle 1 ≃* Multiplicative ℤ:=by
 let:ContractibleSpace ℝ:=inferInstance
 exact (Circle.isAddQuotientCoveringMap_exp.fundamentalGroupEquiv (⟨0,by simp⟩:Circle.exp ⁻¹' {1})).trans
  ((MulEquiv.inv' (Multiplicative (AddSubgroup.zmultiples (2*Real.pi)))).symm.trans
   DB.symm.toMultiplicative)
noncomputable def Y1 (x:c7 2):FundamentalGroup (c7 2) x ≃* Multiplicative ℤ:=
 (lT tO x).trans
  ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (tO x) 1).trans zK)
end EilenbergGanea.CWCollar
namespace EilenbergGanea.CWCollar
open CubicalSingular PathTransport
noncomputable def h8 (x:c7 2):(FundamentalGroup (c7 2) x)ᵐᵒᵖ ≃* Multiplicative ℤ:=
 (Y1 x).op.trans (MulEquiv.inv' (Multiplicative ℤ)).symm
noncomputable def K3 (x:c7 2):E4 (c7 2) x ≃ₗ[ℤ] ℤ:=
 (((h8 x).abelianizationCongr.trans (Abelianization.equivOfComm (H:=Multiplicative ℤ)).symm).toAdditive).toIntLinearEquiv
noncomputable def l9 (x:c7 2):d0 (c7 2) ≃ₗ[ℤ] ℤ:=
 (sI (fun y=>(PathConnectedSpace.joined x y).somePath)).trans (K3 x)
noncomputable def d3 (x:c7 2):Path x x:=
 Quotient.out ((h8 x).symm (Multiplicative.ofAdd 1)).unop
theorem QI (x:c7 2) :
  h8 x (MulOpposite.op (bR (d3 x)))=Multiplicative.ofAdd 1:=by
 have he:bR (d3 x)=((h8 x).symm (Multiplicative.ofAdd 1)).unop:=Quotient.out_eq _
 rw [he,MulOpposite.op_unop,MulEquiv.apply_symm_apply]
theorem Y3 (x:c7 2) (p:Path x x) :
  ∃ n:ℤ,MulOpposite.op (bR p)=(MulOpposite.op (bR (d3 x)):(FundamentalGroup (c7 2) x)ᵐᵒᵖ) ^ n:=by
 refine ⟨(h8 x (MulOpposite.op (bR p))).toAdd,?_⟩
 apply (h8 x).injective
 rw [map_zpow,QI]
 apply Multiplicative.toAdd.injective
 rw [toAdd_zpow]
 change _=_ • (1:ℤ)
 simp
def Bl {X:Type*} [TopologicalSpace X] {x:X} (p:Path x x):l5 (Set.univ:Set X):=
 ⟨gen₁ p.toContinuousMap,by rw [Gk]; trivial,by
  change d₁ (gen₁ p.toContinuousMap)=0
  simp only [gen₁,O5,KI,one_smul]
  change Finsupp.single (p 1) (1:ℤ) - Finsupp.single (p 0) (1:ℤ)=0
  rw [p.target,p.source,sub_self]⟩
def z1 {X:Type*} [TopologicalSpace X] {x:X} (p:Path x x):d0 X:=
 (boundaries Set.univ).mkQ (Bl p)
theorem QJ {X:Type*} [TopologicalSpace X] {r x:X}
  (q:∀ y,Path r y) (p:Path x x) :
  sI q (z1 p)=Additive.ofMul (Abelianization.of (c0 q p)):=by
 change jR q (gen₁ p.toContinuousMap)=_
 rw [Qy]
 simp only [f6,u2]
theorem Y4 (x:c7 2) :
  z1 (d3 x)=(l9 x).symm 1:=by
 apply (l9 x).injective
 rw [LinearEquiv.apply_symm_apply]
 change K3 x (sI _ (z1 _))=1
 rw [QJ]
 have he (w:(FundamentalGroup (c7 2) x)ᵐᵒᵖ) :
   K3 x (Additive.ofMul (Abelianization.of w))=(h8 x w).toAdd:=by
  rfl
 rw [he]
 have hb:=Qz (fun y=>(PathConnectedSpace.joined x y).somePath) (bR (d3 x))
 have hh:=congrArg (fun z=>K3 x (Additive.ofMul z)) hb
 rw [he,he] at hh
 change (h8 x (based _ (bR (d3 x)))).toAdd=1
 rw [hh,QI]
 rfl
end EilenbergGanea.CWCollar
end
noncomputable section
open Classical Set Metric Topology
namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable {J:Type*}
abbrev fiberInclusion (j:J):C(Y,Σ _:J,Y):=ContinuousMap.sigmaMk (X:=fun _:J=>Y) j
def qX:C((Σ _:J,Y),Y):=⟨Sigma.snd,continuous_sigma (fun _=>continuous_id)⟩
variable {r:Y} (q:∀ y,Path r y)
/-- Close each edge within its own fiber and record the cycle at that index. -/
def j9:N₁ (Σ _:J,Y) →ₗ[ℤ] (J →₀ l5 (univ:Set Y)):=
 (D₁ _).liftQ (Finsupp.linearCombination ℤ (fun σ:a5 (Σ _:J,Y)=>
  Finsupp.single (σ 0).1 (oW q (gen₁ (qX.comp σ))))) (by
   apply Submodule.span_le.mpr
   rintro _ ⟨⟨j,y⟩,rfl⟩
   simp [gQ,show qX.comp (ContinuousMap.const I (Sigma.mk j y)) = ContinuousMap.const I y from rfl])
@[simp] theorem FH (j:J) (c:N₁ Y) :
  j9 q (c3 (fiberInclusion j) c)=Finsupp.single j (oW q c):=by
 apply LinearMap.congr_fun (f:=(j9 q).comp (c3 (fiberInclusion j))) (g:=(Finsupp.lsingle j).comp (oW q)) _ c
 ext σ:3
 change j9 q (c3 _ (gen₁ σ))=_
 rw [KQ]; simp [j9,gen₁,show qX.comp ((fiberInclusion j).comp σ)=σ from rfl]
def Eh:=Finsupp.lsum ℤ (fun j:J=>qB (fiberInclusion (Y:=Y) j) (mapsTo_univ _ univ))
theorem FU (z:l5 (univ:Set (Σ _:J,Y))):Eh (j9 q z.val)=z:=by
 let anchor:=Finsupp.linearCombination ℤ (fun x:Σ _:J,Y=>c3 (fiberInclusion x.1) (gen₁ (q x.2).toContinuousMap))
 let U:=(l5 univ).subtype.comp (Eh.comp (j9 (J:=J) q))
 have eq:U.comp (D₁ _).mkQ = (LinearMap.id - anchor.comp d₁).comp (D₁ _).mkQ:=by
  ext σ
  obtain ⟨j,τ,rfl⟩:=σ.exists_lift_sigma
  change U (gen₁ ((fiberInclusion j).comp τ))=gen₁ _ - anchor (b₁ (Finsupp.single _ 1))
  rw [← KQ]
  simp only [U,LinearMap.comp_apply,FH,Eh,Finsupp.lsum_single]
  change c3 _ (gen₁ τ - anchors q (b₁ (Finsupp.single τ 1)))=_
  simp [anchor,anchors]
 apply Subtype.ext
 obtain ⟨c,hc⟩:=(D₁ _).mkQ_surjective z.val
 change U z.val=z.val
 have hz:d₁ z.val=0:=z.property.2
 simpa only [LinearMap.comp_apply,hc,LinearMap.sub_apply,LinearMap.id_apply,hz,map_zero,sub_zero] using LinearMap.congr_fun eq c
def k6:=(Finsupp.mapRange.linearMap (α:=J) (boundaries (univ:Set Y)).mkQ).comp (j9 q)
def E9:d0 (Σ _:J,Y) →ₗ[ℤ] (J →₀ d0 Y):=
 (boundaries univ).liftQ ((k6 q).comp (l5 univ).subtype) (by
  rintro z ⟨b,_,hb⟩
  change k6 q z.val=0
  change d₂ b=z.val at hb
  rw [← hb]; obtain ⟨b,rfl⟩:=(D₂ _).mkQ_surjective b
  apply LinearMap.congr_fun (g:=0) (f:=((k6 q).comp d₂).comp (D₂ _).mkQ) _ b
  ext σ:2
  obtain ⟨j,τ,rfl⟩:=σ.exists_lift_sigma
  change k6 q (d₂ (gen₂ ((fiberInclusion j).comp τ)))=0
  rw [← Xt,Gd]; simp [k6,show ∀ w:N₁ Y,(boundaries univ).mkQ (oW q w)=g6 q w from fun _=>rfl])
def assembly:=Finsupp.lsum ℤ (fun j:J=>gG (fiberInclusion (Y:=Y) j))
def zY:(J →₀ d0 Y) ≃ₗ[ℤ] d0 (Σ _:J,Y):=
 LinearEquiv.ofLinearMap assembly (E9 q) (by
  apply LinearMap.ext; intro h; obtain ⟨z,rfl⟩:=(boundaries univ).mkQ_surjective h
  change assembly ((Finsupp.mapRange.linearMap _) (j9 q z.val))=_
  conv_rhs=>rw [← FU q z]
  generalize j9 q z.val=c
  induction c using Finsupp.induction_linear with
  | zero=>simp
  | add _ _ ha hb=>simp only [map_add,ha,hb]
  | single j x=>simp [assembly,Eh,gG]; rfl) (by
  apply Finsupp.lhom_ext; intro j h
  obtain ⟨z,rfl⟩:=(boundaries univ).mkQ_surjective h
  simp only [assembly,LinearMap.comp_apply,Finsupp.lsum_single,LinearMap.id_apply]
  change k6 q (c3 (fiberInclusion j) z.val)=_
  simp [k6,show (boundaries univ).mkQ (oW q z.val)=_ from zG q z])
def Bm [PathConnectedSpace Y] (y₀:Y) (e:d0 Y ≃ₗ[ℤ] ℤ) :
  (J →₀ ℤ) ≃ₗ[ℤ] d0 (Σ _:J,Y):=
 (Finsupp.mapRange.linearEquiv e.symm).trans
  (zY (fun y=>(PathConnectedSpace.joined y₀ y).somePath))
end EilenbergGanea.CubicalSingular
namespace EilenbergGanea.PathTransport
open Set CubicalSingular
variable {X G:Type*} [TopologicalSpace X] [Group G]
def jT {Y:Type*} [TopologicalSpace Y] (U:Set X) (γ:C(Y,X))
  (h:Set.range γ ⊆ U):C(Y,U):=⟨fun t=>⟨γ t,h ⟨t,rfl⟩⟩,γ.continuous.subtype_mk _⟩
structure Flat (X G:Type*) [TopologicalSpace X] [Group G] where
 value:a5 X → G
 constant:∀ x,value (ContinuousMap.const I x)=1
 split:∀ γ,value γ=value (jG γ false) * value (jG γ true)
 square:∀ σ,value (e4 σ 0) * value (eW σ 1)=value (eW σ 0) * value (e4 σ 1)
def Flat.coboundary (f:X → G):Flat X G where
 value γ:=(f (γ 0))⁻¹ * f (γ 1)
 constant _:=inv_mul_cancel _
 split γ:=by simp only [jG,ContinuousMap.coe_comp,Function.comp_apply,j3,m4,EU]; group
 square σ:=by simp only [eW,e4,ContinuousMap.coe_mk]; group
def Flat.ofHom {r:X} (q:∀ x,Path r x) (ρ:(FundamentalGroup X r)ᵐᵒᵖ →* G):Flat X G where
 value γ:=ρ (g2 q γ)
 constant x:=by rw [Yj,map_one]
 split γ:=(congrArg ρ (Yk q γ)).trans (map_mul ρ _ _)
 square σ:=(map_mul ρ _ _).symm.trans ((congrArg ρ (Qo q σ)).trans (map_mul ρ _ _))
structure PatchPair (U V:Set X) where
 left:Flat U G
 right:Flat V G
 agree:∀ (γ:a5 X) (h:Set.range γ ⊆ U) (k:Set.range γ ⊆ V),
  left.value (jT U γ h)=right.value (jT V γ k)
namespace PatchPair
variable {U V:Set X} (a:PatchPair (G:=G) U V)
def value (γ:a5 X):G:=if h:Set.range γ ⊆ U then a.left.value (jT U γ h)
 else if k:Set.range γ ⊆ V then a.right.value (jT V γ k) else 1
theorem f5 (γ:a5 X) (h:Set.range γ ⊆ U):a.value γ=a.left.value (jT U γ h):=dif_pos h
theorem f7 (γ:a5 X) (k:Set.range γ ⊆ V):a.value γ=a.right.value (jT V γ k):=by
 unfold value
 split_ifs with h
 ·exact a.agree γ h k
 ·rfl
theorem restriction (W) (h:W ∈ ({U,V}:Set (Set X))) :
  ∃ d:Flat W G,∀ γ k,a.value γ=d.value (jT W γ k):=by
 rcases h with rfl | rfl
 ·exact ⟨a.left,a.f5⟩
 ·exact ⟨a.right,a.f7⟩
def system:Local (G:=G) ({U,V}:Set (Set X)) where
  value:=a.value
  constant x:=by
    unfold value
    split_ifs with h k
    · exact a.left.constant ⟨x,h ⟨0,rfl⟩⟩
    · exact a.right.constant ⟨x,k ⟨0,rfl⟩⟩
    · rfl
  split γ:=by
    rintro ⟨W,hW,h⟩
    obtain ⟨d,e⟩:=a.restriction W hW
    rw [e γ h,e _ (fun _ ⟨t,ht⟩=>h ⟨half false t,ht⟩),e _ (fun _ ⟨t,ht⟩=>h ⟨half true t,ht⟩)]
    exact d.split (jT W γ h)
  bx8 σ:=by
    rintro ⟨W,hW,h⟩
    obtain ⟨d,e⟩:=a.restriction W hW
    rw [e _ (fun _ ⟨t,ht⟩=>h ⟨(t,0),ht⟩),e _ (fun _ ⟨t,ht⟩=>h ⟨(1,t),ht⟩),
      e _ (fun _ ⟨t,ht⟩=>h ⟨(0,t),ht⟩),e _ (fun _ ⟨t,ht⟩=>h ⟨(t,1),ht⟩)]
    exact d.square (jT W σ h)
theorem Fd {Y:Type*} [MetricSpace Y] (γ:C(Y,X))
  (h:γ ∈ CubicalMesh.small ({U,V}:Set (Set X))):Set.range γ ⊆ U \/ Set.range γ ⊆ V:=by
 rcases h with ⟨W,hW,hγ⟩
 simp only [mem_insert_iff,mem_singleton_iff] at hW
 rcases hW with rfl | rfl
 ·exact Or.inl hγ
 ·exact Or.inr hγ
theorem MQ (hU:IsOpen U) (hV:IsOpen V):∀ W ∈ ({U,V}:Set (Set X)),IsOpen W:=by
 rintro W (rfl | rfl)
 ·exact hU
 ·exact hV
omit [TopologicalSpace X] in
theorem MW (hUV:U ∪ V=univ):⋃₀ ({U,V}:Set (Set X))=univ:=by
 simpa only [sUnion_insert,sUnion_singleton] using hUV
def transport (hU:IsOpen U) (hV:IsOpen V) (hUV:U ∪ V=univ):a5 X -> G:=
 a.system.transport (MQ hU hV) (MW hUV)
end PatchPair
end EilenbergGanea.PathTransport
namespace EilenbergGanea.ForestCover
open Set PathTransport CubicalSingular
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
def f0 (Y:Type*) [TopologicalSpace Y]:Prop:=
 ∀ (x y:Y) (p p':Path x y),Path.Homotopic p p'
def JI (x:Y):Y:=(ZerothHomotopy.mk x).out
def lV (x:Y):Path (JI x) x:=
 (Quotient.exact (Quotient.out_eq (ZerothHomotopy.mk x)):Joined (JI x) x).somePath
theorem MY {x y:Y} (p:Path x y):JI x=JI y:=
 congrArg Quotient.out (ZerothHomotopy.sound p)
variable {r:X} (q:∀ x,Path r x)
def e0 (f:C(Y,X)) (x:Y):(FundamentalGroup X r)ᵐᵒᵖ:=
 c0 q ((lV x).map f.continuous)
theorem MZ (hY:f0 Y) (f:C(Y,X)) {x y:Y} (p:Path x y) :
  g2 q (p.map f.continuous).toContinuousMap=(e0 q f x)⁻¹ * e0 q f y:=by
 have h:=(hY _ _ ((lV x).trans p)
  ((lV y).cast (MY p) rfl)).map f
 have he:=s3 q h
 rw [Path.map_trans,l4] at he
 have hy:c0 q (((lV y).cast (MY p) rfl).map f.continuous)=e0 q f y:=
  f3 q _ _ (fun _=>rfl)
 rw [hy] at he
 rw [u2]
 exact (eq_inv_mul_iff_mul_eq.mpr he)
variable (U V:Set X)
def inclusion (U:Set X):C(U,X):=⟨Subtype.val,continuous_subtype_val⟩
def gauge (x:X):(FundamentalGroup X r)ᵐᵒᵖ:=
 if h:x ∈ U then e0 q (inclusion U) ⟨x,h⟩
 else if h:x ∈ V then e0 q (inclusion V) ⟨x,h⟩ else 1
def qZ (x:(U ∩ V:Set X)):(FundamentalGroup X r)ᵐᵒᵖ:=
 e0 q (inclusion V) ⟨x.val,x.property.2⟩ *
  (e0 q (inclusion U) ⟨x.val,x.property.1⟩)⁻¹
theorem Eb {G:Type*} [Group G] {a b c d:G} (h:a⁻¹*b=c⁻¹*d):c*a⁻¹=d*b⁻¹:=by
  calc c*a⁻¹ = c*(a⁻¹*b)*b⁻¹:=by group
       _ = d*b⁻¹:=by rw [h]; group
theorem Y6 (hU:f0 U) (hV:f0 V)
  {x y:(U ∩ V:Set X)} (p:Path x y):qZ q U V x=qZ q U V y:=by
 apply Eb
 exact (MZ q hU (inclusion U) (p.map (continuous_subtype_val.subtype_mk (fun z=>z.property.1)))).symm.trans
  (MZ q hV (inclusion V) (p.map (continuous_subtype_val.subtype_mk (fun z=>z.property.2))))
def evaluation (hU:f0 U) (hV:f0 V) :
  FreeGroup (ZerothHomotopy (U ∩ V:Set X)) →* (FundamentalGroup X r)ᵐᵒᵖ:=
 FreeGroup.lift (ZerothHomotopy.lift (qZ q U V) (fun _ _ p=>Y6 q U V hU hV p))
def mC (x:X):FreeGroup (ZerothHomotopy (U ∩ V:Set X)):=
 if h:x ∈ U ∩ V then FreeGroup.of (ZerothHomotopy.mk ⟨x,h⟩) else 1
@[simp] theorem M4 (x:(U ∩ V:Set X)) :
  mC U V x.val=FreeGroup.of (ZerothHomotopy.mk x):=dif_pos x.property
def labels:PatchPair (G:=FreeGroup (ZerothHomotopy (U ∩ V:Set X))) U V where
 left:=Flat.coboundary fun _=>1
 right:=Flat.coboundary fun x=>mC U V x.val
 agree:=by
  intro γ h k
  let hγ:Set.range γ ⊆ U ∩ V:=fun _ hx=>⟨h hx,k hx⟩
  change 1⁻¹ * 1 = (mC U V (γ 0))⁻¹ * mC U V (γ 1)
  have he:ZerothHomotopy.mk (⟨γ 0,hγ ⟨0,rfl⟩⟩:(U ∩ V:Set X)) = ZerothHomotopy.mk ⟨γ 1,hγ ⟨1,rfl⟩⟩:=
   ZerothHomotopy.sound (kV (jT _ γ hγ))
  rw [M4 U V ⟨γ 0,hγ ⟨0,rfl⟩⟩,M4 U V ⟨γ 1,hγ ⟨1,rfl⟩⟩,he]
  simp
end EilenbergGanea.ForestCover
namespace EilenbergGanea.PathTransport
open Set CubicalSingular ForestCover
variable {X G:Type*} [TopologicalSpace X] [Group G]
@[simp] theorem QN {r x y:X} (q:∀ z,Path r z) (p:Path x y) :
  c0 q p.symm=(c0 q p)⁻¹:=by
 apply eq_inv_of_mul_eq_one_left
 rw [<- l4]
 exact (s3 q (Path.Homotopic.symm_trans p)).trans (Qn q _)
variable {U V:Set X} {r:U} (q:∀ x:U,Path r x) (ρ:(FundamentalGroup U r)ᵐᵒᵖ →* G)
def gN:C((U ∩ V:Set X),U):=⟨fun z=>⟨z.val,z.property.1⟩,continuous_subtype_val.subtype_mk _⟩
def oO:Prop:=∀ (z:(U ∩ V:Set X)) (p:Path z z),ρ (c0 q (p.map gN.continuous))=1
theorem Y7 (hk:oO (V:=V) q ρ)
  {x y:(U ∩ V:Set X)} (p:Path x y) :
  ρ (c0 q (p.map gN.continuous)) =
   (ρ (e0 q gN x))⁻¹ * ρ (e0 q gN y):=by
 let sy:=(lV y).cast (MY p) rfl
 have h:=hk (JI x) (((lV x).trans p).trans sy.symm)
 rw [Path.map_trans,Path.map_trans,<- Path.map_symm] at h
 simp only [l4,QN,map_mul,map_inv] at h
 have he:c0 q (sy.map gN.continuous)=e0 q gN y:=
  f3 q _ _ (fun _=>rfl)
 rw [he] at h
 change ρ (e0 q gN x) * _ * (ρ (e0 q gN y))⁻¹=1 at h
 apply eq_inv_mul_iff_mul_eq.mpr
 exact mul_inv_eq_one.mp h
def K4 (x:X):G:=
 if h:x ∈ U ∩ V then ρ (e0 q gN ⟨x,h⟩) else 1
@[simp] theorem QO (x:(U ∩ V:Set X)) :
  K4 (V:=V) q ρ x.val=ρ (e0 q gN x):=dif_pos x.property
def patched (hk:oO (V:=V) q ρ):PatchPair (G:=G) U V where
 left:=Flat.ofHom q ρ
 right:=Flat.coboundary fun x=>K4 q ρ x.val
 agree γ h k:=by
  let hc:Set.range γ ⊆ U ∩ V:=fun _ hx=>⟨h hx,k hx⟩
  change ρ (g2 q (jT U γ h)) = (K4 q ρ (γ 0))⁻¹ * K4 q ρ (γ 1)
  let p:=kV (jT (U ∩ V) γ hc)
  rw [QO q ρ ⟨γ 0,hc ⟨0,rfl⟩⟩,QO q ρ ⟨γ 1,hc ⟨1,rfl⟩⟩]
  exact Y7 q ρ hk p
theorem Ec (hU:IsOpen U) (hV:IsOpen V) (hc:U ∪ V=univ)
  (hk:oO (V:=V) q ρ) (p:Path r r)
  (hp:(p.map continuous_subtype_val).Homotopic (Path.refl r.val)) :
  ρ (c0 q p)=1:=by
 let a:=patched q ρ hk
 have he:=a.system.Qk (PatchPair.MQ hU hV) (PatchPair.MW hc) hp.some
 change a.system.transport _ _ (p.map continuous_subtype_val).toContinuousMap =
  a.system.transport _ _ (ContinuousMap.const I r.val) at he
 rw [a.system.KR] at he
 have h:Set.range (p.map continuous_subtype_val) ⊆ U:=fun _ ⟨t,ht⟩=>ht ▸ (p t).property
 rw [a.system.Qe _ _ ⟨U,by simp,h⟩] at he
 change a.value _ = 1 at he
 rw [a.f5 _ h] at he
 change ρ (g2 q (jT U _ h)) = 1 at he
 have hh:jT U (p.map continuous_subtype_val).toContinuousMap (fun _ ⟨t,ht⟩=>ht ▸ (p t).property)=p.toContinuousMap:=by
  ext t; rfl
 simpa only [hh,u2] using he
end EilenbergGanea.PathTransport
namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X Y G:Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
variable {r:X} (q:∀ y,Path r y)
def zL (f:C(Y,X)) (y:Y):(FundamentalGroup Y y)ᵐᵒᵖ →* (FundamentalGroup X r)ᵐᵒᵖ where
 toFun w:=based q ((FundamentalGroup.map f y) w.unop)
 map_one':=by
  change based q ((FundamentalGroup.map f y) 1)=1
  rw [map_one]
  exact Qm q _
 map_mul' u v:=by
  change based q ((FundamentalGroup.map f y) (v.unop * u.unop))=_
  rw [map_mul]
  exact Ql q _ _
@[simp] theorem du4 (f:C(Y,X)) {y:Y} (p:Path y y) :
  zL q f y (MulOpposite.op (bR p))=c0 q (p.map f.continuous):=rfl
theorem Y8 [PathConnectedSpace Y] (f:C(Y,X)) (y₀:Y)
  (ρ:(FundamentalGroup X r)ᵐᵒᵖ →* G)
  (h:∀ p:Path y₀ y₀,ρ (c0 q (p.map f.continuous))=1)
  {y:Y} (p:Path y y):ρ (c0 q (p.map f.continuous))=1:=by
 let s:=(PathConnectedSpace.joined y₀ y).somePath
 have hh:=h (s.trans (p.trans s.symm))
 rw [Path.map_trans,Path.map_trans,<- Path.map_symm] at hh
 simp only [l4,QN,map_mul,map_inv] at hh
 rw [<- mul_assoc] at hh
 have he:=mul_inv_eq_one.mp hh
 exact mul_left_cancel (show ρ (c0 q (s.map f.continuous)) *
  ρ (c0 q (p.map f.continuous))=ρ (c0 q (s.map f.continuous)) * 1 by simpa using he)
end EilenbergGanea.PathTransport
namespace EilenbergGanea.CWCollar
open CubicalSingular PathTransport
variable {X G:Type*} [TopologicalSpace X] [Group G] {r:X} (q:∀ y,Path r y)
theorem Y9 (f:C(c7 2,X)) (y₀:c7 2)
  (ρ:(FundamentalGroup X r)ᵐᵒᵖ →* G)
  (h:ρ (c0 q ((d3 y₀).map f.continuous))=1)
  {y:c7 2} (p:Path y y):ρ (c0 q (p.map f.continuous))=1:=by
 apply Y8 q f y₀ ρ _ p
 intro t
 obtain ⟨n,hn⟩:=Y3 y₀ t
 have he:=congrArg (ρ.comp (zL q f y₀)) hn
 change ρ (zL q f y₀ (MulOpposite.op (bR t)))=ρ (zL q f y₀ (_ ^ n)) at he
 rw [map_zpow,map_zpow] at he
 change ρ (c0 q (t.map f.continuous))=ρ (c0 q ((d3 y₀).map f.continuous)) ^ n at he
 rw [h,one_zpow] at he
 exact he
end EilenbergGanea.CWCollar
namespace EilenbergGanea.PathTransport
open CubicalSingular
variable {X Y J G:Type*} [TopologicalSpace X] [TopologicalSpace Y] [Group G]
variable {r:X} (q:∀ y,Path r y)
theorem Zb (f:C((Σ _:J,Y),X))
    (ρ:(FundamentalGroup X r)ᵐᵒᵖ →* G)
    (hk:∀ (j:J) (y:Y) (p:Path y y),
      ρ (c0 q (p.map (f.comp (fiberInclusion j)).continuous))=1)
    {z:(Σ _:J,Y)} (p:Path z z):ρ (c0 q (p.map f.continuous))=1:=by
  obtain ⟨j,τ,h⟩:=p.toContinuousMap.exists_lift_sigma
  let s:=p.map qX.continuous
  rw [← f3 q (s.map (f.comp (fiberInclusion j)).continuous) (p.map f.continuous) (fun t=>by
    have ht:=DFunLike.congr_fun h t
    change f ((fiberInclusion j) (qX (p.toContinuousMap t)))=f (p.toContinuousMap t)
    rw [ht]; rfl)]
  exact hk j _ s
theorem Zd (f:C(X,Y)) {x:X} (p:Path x x)
  (hp:(p.map f.continuous).Homotopic (Path.refl (f x))) :
  (FundamentalGroup.map f r).op (c0 q p)=1:=by
 apply MulOpposite.unop_injective
 change bR ((((q x).trans p).trans (q x).symm).map f.continuous)=Path.Homotopic.Quotient.refl (f r)
 rw [Path.map_trans,Path.map_trans,<- Path.map_symm]
 simp only [bR,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm]
 have hh:Path.Homotopic.Quotient.mk (p.map f.continuous)=Path.Homotopic.Quotient.refl (f x):=Path.Homotopic.Quotient.eq.mpr hp
 rw [hh]
 simp only [Path.Homotopic.Quotient.trans_refl,Path.Homotopic.Quotient.trans_symm]
end EilenbergGanea.PathTransport
namespace EilenbergGanea.CWCollar.Attachment
open Set CubicalSingular PathTransport
variable {X J:Type*} [TopologicalSpace X] (a:Attachment X J 2)
variable {r:a.outer} (q:∀ y,Path r y) (y₀:c7 2)
def g3 (j:J):C(c7 2,a.outer):=
 gN.comp ((a.cZ:C((Σ _:J,c7 2),(a.outer ∩ a.inner:Set X))).comp (fiberInclusion j))
def kH (j:J):(FundamentalGroup a.outer r)ᵐᵒᵖ:=
 c0 q ((d3 y₀).map (a.g3 j).continuous)
theorem Ze {G:Type*} [Group G]
  (ρ:(FundamentalGroup a.outer r)ᵐᵒᵖ →* G)
  (h:∀ j,ρ (a.kH q y₀ j)=1):oO (V:=a.inner) q ρ:=by
 intro z p
 let f:C((Σ _:J,c7 2),a.outer):=gN.comp (a.cZ:C((Σ _:J,c7 2),(a.outer ∩ a.inner:Set X)))
 let t:=p.map a.cZ.symm.continuous
 have hh:=Zb q f ρ (fun j y s=>Y9 q (a.g3 j) y₀ ρ (h j) s) t
 have he:=f3 q (t.map f.continuous) (p.map gN.continuous) (fun s=>by
  change (⟨(a.cZ (a.cZ.symm (p s))).val,_⟩:a.outer)=_
  exact congrArg (fun z:(a.outer ∩ a.inner:Set X)=>(⟨z.val,z.property.1⟩:a.outer)) (a.cZ.apply_symm_apply (p s)))
 exact (congrArg ρ he).symm.trans hh
theorem Zi (hthin:ForestCover.f0 a.inner) :
  ((FundamentalGroup.map (⟨Subtype.val,continuous_subtype_val⟩:C(a.outer,X)) r).op).ker =
   Subgroup.normalClosure (Set.range (a.kH q y₀)):=by
 let f:C(a.outer,X):=⟨Subtype.val,continuous_subtype_val⟩
 let N:=Subgroup.normalClosure (Set.range (a.kH q y₀))
 let ρ:=QuotientGroup.mk' N
 apply le_antisymm
 ·intro w hw
  obtain ⟨p,hp⟩:=Quotient.exists_rep w.unop
  have hp':MulOpposite.op (bR p)=w:=by
   exact (congrArg MulOpposite.op hp).trans (MulOpposite.op_unop w)
  have hn:(p.map f.continuous).Homotopic (Path.refl r.val):=by
   apply Path.Homotopic.Quotient.eq.mp
   change ((FundamentalGroup.map f r).op (MulOpposite.op (bR p))).unop=(1:FundamentalGroup X r.val)
   rw [hp']
   exact congrArg MulOpposite.unop hw
  have hk:oO (V:=a.inner) q ρ:=a.Ze q y₀ ρ (fun j=>
   (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure ⟨j,rfl⟩))
  have he:=Ec q ρ a.Gm a.Gp a.k7 hk p hn
  let u:(FundamentalGroup a.outer r)ᵐᵒᵖ:=MulOpposite.op (bR (q r))
  have hbased:c0 q p=u * w * u⁻¹:=by
   rw [<- hp']
   rfl
  rw [hbased,map_mul,map_mul,map_inv] at he
  have hh:=mul_inv_eq_one.mp he
  have hf:ρ w=1:=mul_left_cancel (show ρ u * ρ w=ρ u * 1 by simpa using hh)
  exact (QuotientGroup.eq_one_iff _).mp hf
 ·apply Subgroup.normalClosure_le_normal
  rintro w ⟨j,rfl⟩
  apply Zd q f
  let g:C(c7 2,a.inner):=⟨fun z=>⟨(a.cZ ⟨j,z⟩).val,(a.cZ ⟨j,z⟩).property.2⟩,
   (continuous_subtype_val.comp (a.cZ.continuous.comp continuous_sigmaMk)).subtype_mk _⟩
  have h:=(hthin _ _ ((d3 y₀).map g.continuous) (Path.refl (g y₀))).map
   (⟨Subtype.val,continuous_subtype_val⟩:C(a.inner,X))
  exact h
end EilenbergGanea.CWCollar.Attachment
namespace EilenbergGanea.CubicalSingular
open Set
variable {J:Type*}
theorem Zj {Y:Type*} [TopologicalSpace Y] [ContractibleSpace Y]
  (z:N₁ (Σ _:J,Y)) (hz:d₁ z=0):∃ b:N₂ (Σ _:J,Y),d₂ b=z:=by
 let r:=(id_nullhomotopic Y).choose
 let e:=zY (J:=J) (fun y=>(PathConnectedSpace.joined r y).somePath)
 let w:l5 univ:=⟨z,by rw [Gk]; trivial,hz⟩
 have h:(boundaries univ).mkQ w=0:=by
  apply e.symm.injective; rw [map_zero]; ext j
  obtain ⟨v,hv⟩:=(boundaries (univ:Set Y)).mkQ_surjective (e.symm ((boundaries univ).mkQ w) j)
  obtain ⟨b,hb⟩:=r0 v.val v.property.2
  exact hv ▸ (Submodule.Quotient.mk_eq_zero _).mpr ⟨b,by rw [KV]; trivial,hb⟩
 obtain ⟨b,_,hb⟩:=(Submodule.Quotient.mk_eq_zero _).mp h
 exact ⟨b,hb⟩
end EilenbergGanea.CubicalSingular
namespace EilenbergGanea.CubicalSingular
open Set
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
theorem ch2 (e:X ≃ₜ Y)
  (hX:∀ z:N₁ X,d₁ z=0 -> ∃ b:N₂ X,d₂ b=z)
  (z:N₁ Y) (hz:d₁ z=0):∃ b:N₂ Y,d₂ b=z:=by
 obtain ⟨b,hb⟩:=hX (c3 (⟨e.symm,e.symm.continuous⟩:C(Y,X)) z) (by rw [Md,hz,map_zero])
 refine ⟨e9 (⟨e,e.continuous⟩:C(X,Y)) b,?_⟩
 rw [Gd,hb,<- Me]
 have he:(⟨e,e.continuous⟩:C(X,Y)).comp (⟨e.symm,e.symm.continuous⟩:C(Y,X))=ContinuousMap.id Y:=
  ContinuousMap.ext e.apply_symm_apply
 rw [he,O9]
def iO (U:Set X):l5 (univ:Set U) ≃ₗ[ℤ] l5 U:=
 LinearEquiv.ofBijective (qB (inc U) (fun x _=>x.property)) ⟨fun _ _ h=>
  Subtype.ext (PN (inc U) Subtype.val_injective (congrArg Subtype.val h)),by
  intro z
  obtain ⟨c,hc⟩:=(u9 U).ge z.property.1
  refine ⟨⟨c,by rw [Gk]; trivial,?_⟩,Subtype.ext hc⟩
  apply XF (inc U) Subtype.val_injective
  rw [<- Md,hc,map_zero]
  exact z.property.2⟩
theorem tP (U:Set X):
  (boundaries (univ:Set U)).map (iO U).toLinearMap=boundaries U:=by
 apply le_antisymm (Submodule.map_le_iff_le_comap.mpr (Qr (inc U) (fun x _=>x.property)))
 intro z hz
 obtain ⟨w,rfl⟩:=(iO U).surjective z
 obtain ⟨b,hb,he⟩:=hz
 obtain ⟨c,rfl⟩:=(o4 U).ge hb
 refine ⟨w,⟨c,by rw [KV]; trivial,PN (inc U) Subtype.val_injective ?_⟩,rfl⟩
 exact (Gd _ _).symm.trans he
theorem q5 (U:Set X) (z:l5 (univ:Set U)) :
  z ∈ boundaries univ ↔ iO U z ∈ boundaries U:=by
 rw [← tP U]
 exact ⟨fun h=>⟨z,h,rfl⟩,fun ⟨w,hw,e⟩=>(iO U).injective e ▸ hw⟩
end EilenbergGanea.CubicalSingular
namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover CubicalSingular
variable {X J:Type*} [TopologicalSpace X] {n:ℕ}
def Bn (n:ℕ):p5 n ≃ₜ ball (0:Fin n -> ℝ) 1 where
 toFun z:=⟨z.val.val,by simpa only [mem_ball,dist_zero_right] using z.property⟩
 invFun z:=⟨⟨z.val,ball_subset_closedBall z.property⟩,by simpa only [mem_ball,dist_zero_right] using z.property⟩
 left_inv _:=rfl
 right_inv _:=rfl
 continuous_toFun:=(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
 continuous_invFun:=(continuous_subtype_val.subtype_mk _).subtype_mk _
instance dm2 (n:ℕ):ContractibleSpace (p5 n):=by
 let:ContractibleSpace (ball (0:Fin n -> ℝ) 1):=contractibleSpace_ball (by norm_num)
 exact (Bn n).contractibleSpace
namespace Attachment
variable (a:Attachment X J n)
theorem Zk (z:N₁ a.inner) (hz:d₁ z=0):∃ b:N₂ a.inner,d₂ b=z:=
 ch2 a.j6 Zj z hz
theorem Zl {z:N₁ X} (hz:z ∈ L₁ a.inner) (hd:d₁ z=0) :
  ∃ b ∈ L₂ a.inner,d₂ b=z:=by
 change (⟨z,hz,hd⟩:l5 a.inner) ∈ boundaries a.inner
 rw [← tP]
 obtain ⟨w,hw⟩:=(iO a.inner).surjective (⟨z,hz,hd⟩:l5 a.inner)
 obtain ⟨b,hb⟩:=a.Zk w w.property.2
 exact ⟨w,⟨b,by rw [KV]; trivial,hb⟩,hw⟩
end Attachment
end EilenbergGanea.CWCollar
namespace EilenbergGanea.CWCollar
open Set CubicalSingular PathTransport
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
@[simp] theorem Zm (f:C(X,Y)) {x:X} (p:Path x x) :
  gG f (z1 p)=z1 (p.map f.continuous):=by
 change (boundaries univ).mkQ (qB f _ (Bl p))=(boundaries univ).mkQ (Bl _)
 congr 1
 apply Subtype.ext
 change c3 f (gen₁ p.toContinuousMap)=gen₁ (p.map f.continuous).toContinuousMap
 rw [KQ]
 rfl
namespace Attachment
variable {J:Type*} (a:Attachment X J 2)
def yJ [ContractibleSpace X] :
  d0 (a.outer ∩ a.inner:Set X) ≃ₗ[ℤ] d0 a.outer:=by
 let W:=a.outer ∩ a.inner
 let f:C(W,a.outer):=gN
 let F:=qB f (mapsTo_univ _ univ)
 have comm (z:l5 (univ:Set W)) :
   (iO a.outer (F z)).val=(iO W z).val:=by
  change c3 (inc a.outer) (c3 f z.val)=_
  rw [← Me]
  rfl
 refine LinearEquiv.ofBijective (gG f) ⟨LinearMap.ker_eq_bot.mp (le_antisymm ?_ bot_le),?_⟩
 ·intro x hx
  obtain ⟨z,rfl⟩:=(boundaries univ).mkQ_surjective x
  change (boundaries univ).mkQ (F z)=0 at hx
  obtain ⟨b,hb,he⟩:=(q5 _ _).mp ((Submodule.Quotient.mk_eq_zero _).mp hx)
  let t:=iO W z
  obtain ⟨c,hc,hd⟩:=a.Zl (XB Set.inter_subset_right t.property.1) t.property.2
  change (boundaries univ).mkQ z=0
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (q5 _ _).mpr
  exact wJ _ _ a.Gm a.Gp a.k7 t.property.1 hb hc (he.trans (comm z)) hd
 ·intro x
  obtain ⟨z,rfl⟩:=(boundaries univ).mkQ_surjective x
  let t:=iO a.outer z
  obtain ⟨c,hc,hd,⟨b,hb,he⟩,_⟩:=v8 _ _ a.Gm a.Gp a.k7 t.property.1 t.property.2
  obtain ⟨w,hw⟩:=(iO W).surjective (⟨c,hc,hd⟩:l5 W)
  refine ⟨(boundaries univ).mkQ w,?_⟩
  change (boundaries univ).mkQ (F w)=(boundaries univ).mkQ z
  rw [← sub_eq_zero,← map_sub]
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  apply (q5 _ _).mpr
  rw [map_sub]
  exact ⟨b,hb,by simpa only [Submodule.subtype_apply,Submodule.coe_sub,comm,hw] using he⟩
def wB [ContractibleSpace X] (y₀:c7 2) :
  (J →₀ ℤ) ≃ₗ[ℤ] d0 a.outer:=
 (Bm y₀ (l9 y₀)).trans
  ((Cv a.cZ).trans a.yJ)
theorem Zn [ContractibleSpace X] (y₀:c7 2) (j:J) :
  a.wB y₀ (Finsupp.single j 1)=z1 ((d3 y₀).map (a.g3 j).continuous):=by
 simp only [wB,LinearEquiv.trans_apply]
 change gG _ (gG _ (assembly ((Finsupp.mapRange.linearEquiv
  (l9 y₀).symm) (Finsupp.single j 1))))=_
 simp only [Finsupp.mapRange.linearEquiv_apply,Finsupp.mapRange_single,assembly,Finsupp.lsum_single]
 rw [<- LinearMap.comp_apply,<- m9,<- LinearMap.comp_apply,<- m9]
 rw [<- Y4,Zm]
 rfl
end Attachment
end EilenbergGanea.CWCollar
namespace EilenbergGanea.PathTransport.Local
open Set CubicalSingular
variable {X G H:Type*} [TopologicalSpace X] [Group G] [Group H]
variable {U:Set (Set X)} (l:Local (G:=G) U) (φ:G →* H)
theorem DG (hU:∀ W ∈ U,IsOpen W) (hc:⋃₀ U=univ) (d:Flat X H) (u:X → H)
  (agree:∀ γ ∈ CubicalMesh.small U,φ (l.value γ)=u (γ 0) * d.value γ * (u (γ 1))⁻¹)
  (γ:a5 X):φ (l.transport hU hc γ)=u (γ 0) * d.value γ * (u (γ 1))⁻¹:=by
 suffices ∀ n γ,pO (U:=U) n γ → φ (l.fold n γ)=u (γ 0) * d.value γ * (u (γ 1))⁻¹ by
  exact this _ γ (Qd hU hc γ)
 intro n
 induction n with
 | zero=>exact agree
 | succ n ih=>
  intro γ h
  change φ (l.fold n _ * l.fold n _) = _
  rw [map_mul,ih (jG γ false) (h false),ih (jG γ true) (h true),d.split γ]
  simp only [jG,ContinuousMap.coe_comp,Function.comp_apply,j3,m4,EU]
  group
end EilenbergGanea.PathTransport.Local
namespace EilenbergGanea.ForestCover
open Set PathTransport CubicalSingular
variable {X:Type*} [TopologicalSpace X] {r:X} (q:∀ x,Path r x) (U V:Set X)
variable (hU:f0 U) (hV:f0 V)
theorem QS (x:X) (hx:x ∈ V) :
  evaluation q U V hU hV (mC U V x)=e0 q (inclusion V) ⟨x,hx⟩ * (gauge q U V x)⁻¹:=by
 by_cases hu:x ∈ U
 ·rw [M4 U V ⟨x,hu,hx⟩]
  simp only [evaluation,FreeGroup.lift_apply_of,ZerothHomotopy.lift_mk,qZ,gauge,dif_pos hu]
 ·have hnot:x ∉ U ∩ V:=fun h=>hu h.1
  simp only [mC,dif_neg hnot,map_one,gauge,dif_neg hu,dif_pos hx,mul_inv_cancel]
theorem QV (W:Set X) (hW:f0 W) (γ:a5 X) (hγ:Set.range γ ⊆ W) :
  g2 q γ=(e0 q (inclusion W) ⟨γ 0,hγ ⟨0,rfl⟩⟩)⁻¹ *
   e0 q (inclusion W) ⟨γ 1,hγ ⟨1,rfl⟩⟩:=by
 exact MZ q hW (inclusion W) (kV (jT W γ hγ))
theorem QW (hUo:IsOpen U) (hVo:IsOpen V) (hc:U ∪ V=univ) (p:Path r r) :
  evaluation q U V hU hV ((labels U V).transport hUo hVo hc p.toContinuousMap)=
   gauge q U V r * c0 q p * (gauge q U V r)⁻¹:=by
 let φ:=evaluation q U V hU hV
 suffices ∀ γ,φ ((labels U V).transport hUo hVo hc γ)=
   gauge q U V (γ 0) * g2 q γ * (gauge q U V (γ 1))⁻¹ by
  simpa using this p.toContinuousMap
 apply (labels U V).system.DG φ _ _ (Flat.ofHom q (MonoidHom.id _))
 intro γ h
 change φ ((labels U V).value γ)=_ * g2 q γ * _
 rcases PatchPair.Fd γ h with h | h
 ·rw [(labels U V).f5 γ h,QV q U hU γ h]
  simp [Flat.coboundary,labels,gauge,dif_pos (h ⟨0,rfl⟩),dif_pos (h ⟨1,rfl⟩)]
 ·rw [(labels U V).f7 γ h,QV q V hV γ h]
  change φ ((mC U V (γ 0))⁻¹ * mC U V (γ 1))=_
  rw [map_mul,map_inv,QS q U V hU hV _ (h ⟨0,rfl⟩),QS q U V hU hV _ (h ⟨1,rfl⟩)]
  group
theorem Zo:Function.Injective (fun g:FundamentalGroup X r=>based q g):=by
 intro g h he
 have he:=congrArg MulOpposite.unop he
 let u:FundamentalGroup X r:=bR (q r)
 change u⁻¹ * (g * u)=u⁻¹ * (h * u) at he
 exact mul_right_cancel (mul_left_cancel he)
include q hU hV in
theorem Zp (hUo:IsOpen U) (hVo:IsOpen V) (hc:U ∪ V=univ) :
  IsFreeGroup (FundamentalGroup X r):=by
 let f:=(labels U V).system.Dz (PatchPair.MQ hUo hVo) (PatchPair.MW hc) r
 have hinj:Function.Injective f:=by
  intro g h he
  obtain ⟨p,rfl⟩:=Quotient.exists_rep g
  obtain ⟨s,rfl⟩:=Quotient.exists_rep h
  have hv:(labels U V).transport hUo hVo hc p.toContinuousMap =
    (labels U V).transport hUo hVo hc s.toContinuousMap:=MulOpposite.op_injective he
  have he':=congrArg (evaluation q U V hU hV) hv
  rw [QW q U V hU hV hUo hVo hc,QW q U V hU hV hUo hVo hc] at he'
  exact Zo q (mul_left_cancel (mul_right_cancel he'))
 let:IsFreeGroup (FreeGroup (ZerothHomotopy (U ∩ V:Set X)))ᵐᵒᵖ:=
  IsFreeGroup.ofMulEquiv (MulEquiv.inv' _)
 exact IsFreeGroup.ofMulEquiv (MonoidHom.ofInjective hinj).symm
end EilenbergGanea.ForestCover
namespace EilenbergGanea.ForestCover
open CategoryTheory CubicalSingular
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
theorem tQ (f:C(X,Y)) (g:C(Y,X))
  (H:(g.comp f).Homotopy (ContinuousMap.id X)) (hY:f0 Y):f0 X:=by
 let F:=FundamentalGroupoid.map f
 let G:=FundamentalGroupoid.map g
 have ei:F ⋙ G ≅ 𝟭 (FundamentalGroupoid X):=by
  simpa only [F,G,<- FundamentalGroupoid.map_comp,FundamentalGroupoid.map_id] using
   asIso (FundamentalGroupoidFunctor.homotopicMapsNatIso H)
 have:F.Faithful:=Functor.Faithful.of_comp_iso ei
 intro x y p q
 have he:F.map (⟦p⟧:(FundamentalGroupoid.mk x) ⟶ FundamentalGroupoid.mk y) =
   F.map (⟦q⟧:(FundamentalGroupoid.mk x) ⟶ FundamentalGroupoid.mk y):=
  Quotient.sound (hY _ _ (p.map f.continuous) (q.map f.continuous))
 exact Quotient.exact (F.map_injective he)
theorem Zq [DiscreteTopology X]:f0 X:=by
 intro x y p q
 have he:p=q:=Path.ext (funext fun t=>by
  have hp:p t=p 0:=(@inferInstance (PreconnectedSpace I)).constant p.continuous
  have hq:q t=q 0:=(@inferInstance (PreconnectedSpace I)).constant q.continuous
  exact hp.trans ((p.source.trans q.source.symm).trans hq.symm))
 rw [he]
theorem Zr (e:X ≃ₜ Y) (hY:f0 Y):f0 X:=
 tQ e e.symm (by
  have he:(e.symm:C(Y,X)).comp (e:C(X,Y))=ContinuousMap.id X:=ContinuousMap.ext e.left_inv
  rw [he]
  exact ContinuousMap.Homotopy.refl _) hY
end EilenbergGanea.ForestCover
namespace EilenbergGanea.ForestCover
open CubicalSingular CWCollar
variable {X J:Type*} [TopologicalSpace X] {Y:J -> Type*} [∀ j,TopologicalSpace (Y j)]
theorem Zt [∀ j,ContractibleSpace (Y j)]:f0 (Σ j,Y j):=by
 rintro ⟨j,x⟩ ⟨k,y⟩ p q
 obtain ⟨i,g,_,he⟩:=p.continuous.exists_lift_sigma
 have h₀:=congrArg Sigma.fst ((congrFun he 0).symm.trans p.source)
 have h₁:=congrArg Sigma.fst ((congrFun he 1).symm.trans p.target)
 change i=j at h₀
 change i=k at h₁
 subst j; subst k
 have lift (a:Path (Sigma.mk i x) (Sigma.mk i y)) :
   ∃ b:Path x y,b.map (ContinuousMap.sigmaMk (X:=Y) i).continuous=a:=by
  obtain ⟨k,f,hf,h⟩:=a.continuous.exists_lift_sigma
  have e₀:=(congrFun h 0).symm.trans a.source
  have e₁:=(congrFun h 1).symm.trans a.target
  have e:k=i:=congrArg Sigma.fst e₀
  subst k
  refine ⟨⟨⟨f,hf⟩,?_,?_⟩,Path.ext (funext fun t=>(congrFun h t).symm)⟩
  ·exact eq_of_heq (Sigma.mk.inj e₀).2
  ·exact eq_of_heq (Sigma.mk.inj e₁).2
 obtain ⟨p',rfl⟩:=lift p
 obtain ⟨q',rfl⟩:=lift q
 exact (SimplyConnectedSpace.paths_homotopic p' q').map (ContinuousMap.sigmaMk (X:=Y) i)
theorem Zu {n:ℕ} (a:Attachment X J n) (hl:f0 a.lower):f0 a.outer:=
 tQ a.l7 a.lB a.yI.symm hl
theorem QX {n:ℕ} (a:Attachment X J n):f0 a.inner:=
 Zr a.j6.symm Zt
include X J in
theorem Zv (a:Attachment X J 1) [DiscreteTopology a.lower]
  {r:X} (q:∀ x,Path r x):IsFreeGroup (FundamentalGroup X r):=
 Zp q a.outer a.inner (Zu a Zq) (QX a)
  a.Gm a.Gp a.k7
end EilenbergGanea.ForestCover
namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover CWCollar
variable {X:Type*} [TopologicalSpace X] [T2Space X] (C:Set X) [CWComplex C]
abbrev Cell (n:ℕ):=RelCWComplex.cell C n
def characteristic {n:ℕ} (i:Cell C n):C(e8 n,C):=
 ⟨fun z=>⟨RelCWComplex.map n i z.val,
  RelCWComplex.closedCell_subset_complex n i ⟨z.val,z.property,rfl⟩⟩,
  (continuousOn_iff_continuous_domRestrict.mp (RelCWComplex.continuousOn n i)).subtype_mk _⟩
abbrev Zw:=Σ c:(Σ n,Cell C n),e8 c.1
def M5:Zw C -> C:=fun c=>characteristic C c.1.2 c.2
omit [T2Space X] in
theorem Zy:Continuous (M5 C):=
 continuous_sigma (fun c=>(characteristic C c.2).continuous)
omit [T2Space X] in
theorem tW:Function.Surjective (M5 C):=by
 intro x
 have hx:x.val ∈ ⋃ (n:ℕ) (i:Cell C n),RelCWComplex.closedCell n i:=by
  rw [CWComplex.union]; exact x.property
 obtain ⟨n,i,z,hz,he⟩:=by simpa only [Set.mem_iUnion,RelCWComplex.closedCell,Set.mem_image] using hx
 exact ⟨⟨⟨n,i⟩,⟨z,hz⟩⟩,Subtype.ext he⟩
theorem wC:IsQuotientMap (M5 C):=by
 apply isQuotientMap_iff_isClosed.mpr
 refine ⟨tW C,fun A=>⟨fun h=>h.preimage (Zy C),?_⟩⟩
 intro hA
 have hc:IsClosed ((Subtype.val:C -> X) '' A):=by
  apply (CWComplex.closed C _ (by rintro _ ⟨x,_,rfl⟩; exact x.property)).mpr
  intro n i
  have hD:IsClosed (characteristic C i ⁻¹' A):=
   hA.preimage (continuous_sigmaMk (i:=(⟨n,i⟩:Σ n,Cell C n)))
  have he:(fun z:e8 n=>(characteristic C i z).val) '' (characteristic C i ⁻¹' A) =
    (Subtype.val '' A) ∩ RelCWComplex.closedCell n i:=by
   ext x
   constructor
   ·rintro ⟨z,hz,rfl⟩
    exact ⟨⟨characteristic C i z,hz,rfl⟩,z.val,z.property,rfl⟩
   ·rintro ⟨⟨y,hy,hxy⟩,z,hz,he⟩
    refine ⟨⟨z,hz⟩,?_,he⟩
    have h:characteristic C i ⟨z,hz⟩=y:=Subtype.ext (he.trans hxy.symm)
    simpa only [mem_preimage,h] using hy
  rw [<- he]
  exact (hD.isCompact.image (continuous_subtype_val.comp (characteristic C i).continuous)).isClosed
 have hpre:=hc.preimage (continuous_subtype_val:Continuous (Subtype.val:C -> X))
 simpa only [Set.preimage_image_eq _ Subtype.val_injective] using hpre
def lower (m:ℕ):Set C:=Subtype.val ⁻¹' (CWComplex.skeletonLT C m:Set X)
theorem M6 {k m:ℕ} (hk:k < m) (i:Cell C k) (z:e8 k) :
  characteristic C i z ∈ lower C m:=by
 apply RelCWComplex.skeletonLT_mono (show (k:ℕ∞)+1 <= (m:ℕ∞) by exact_mod_cast Nat.succ_le_of_lt hk)
  (RelCWComplex.closedCell_subset_skeletonLT k i (show (characteristic C i z).val ∈ RelCWComplex.closedCell k i from ?_))
 exact ⟨z.val,z.property,rfl⟩
def M7 (m:ℕ):lower C m ⊕ (Σ _:Cell C m,e8 m) -> C:=
 Sum.elim Subtype.val (fun c=>characteristic C c.1 c.2)
theorem Zz (m:ℕ):Continuous (M7 C m):=
 continuous_subtype_val.sumElim (continuous_sigma (fun i=>(characteristic C i).continuous))
theorem BT (m:ℕ) (hd:∀ k,m < k -> IsEmpty (Cell C k)) :
  Function.Surjective (M7 C m):=by
 intro x
 obtain ⟨⟨⟨k,i⟩,z⟩,rfl⟩:=tW C x
 by_cases hk:k < m
 ·exact ⟨.inl ⟨characteristic C i z,M6 C hk i z⟩,rfl⟩
 ·have hkm:k=m:=by
   by_contra h
   have:=hd k (by omega)
   exact isEmptyElim i
  subst k
  exact ⟨.inr ⟨i,z⟩,rfl⟩
theorem C8 (m:ℕ) (hd:∀ k,m < k -> IsEmpty (Cell C k)) :
  IsQuotientMap (M7 C m):=by
 apply isQuotientMap_iff_isClosed.mpr
 refine ⟨BT C m hd,fun A=>⟨fun h=>h.preimage (Zz C m),?_⟩⟩
 intro hA
 apply (wC C).isClosed_preimage.mp
 rw [isClosed_sigma_iff]
 rintro ⟨k,i⟩
 by_cases hk:k < m
 ·let f:e8 k -> lower C m ⊕ (Σ _:Cell C m,e8 m):=
   fun z=>.inl ⟨characteristic C i z,M6 C hk i z⟩
  exact hA.preimage (continuous_inl.comp ((characteristic C i).continuous.subtype_mk (M6 C hk i)))
 ·have hkm:k=m:=by
   by_contra h
   have:=hd k (by omega)
   exact isEmptyElim i
  subst k
  exact hA.preimage (continuous_inr.comp (continuous_sigmaMk (i:=i)))
def zO (m:ℕ) (hd:∀ k,m < k -> IsEmpty (Cell C k)):Attachment C (Cell C m) m where
 lower:=lower C m
 ck1:=(CWComplex.skeletonLT C m).closed'.preimage continuous_subtype_val
 l0:=characteristic C
 boundary:=by
  intro i z hz
  exact RelCWComplex.cellFrontier_subset_skeletonLT m i
   ⟨z.val,by simpa only [mem_sphere,dist_zero_right] using hz,rfl⟩
 interior:=by
  intro i z hz hl
  exact Set.disjoint_left.mp (RelCWComplex.disjoint_skeletonLT_openCell le_rfl) hl
   ⟨z.val,by simpa only [mem_ball,dist_zero_right] using hz,rfl⟩
 disjoint:=by
  intro i j z w hz hw he
  have he:=congrArg Subtype.val he
  have hz':z.val ∈ ball (0:Fin m -> ℝ) 1:=by simpa only [mem_ball,dist_zero_right] using hz
  have hw':w.val ∈ ball (0:Fin m -> ℝ) 1:=by simpa only [mem_ball,dist_zero_right] using hw
  by_cases hij:i=j
  ·subst j
   refine ⟨rfl,Subtype.ext ((RelCWComplex.map m i).injOn ?_ ?_ he)⟩
   ·simpa only [RelCWComplex.source_eq] using hz'
   ·simpa only [RelCWComplex.source_eq] using hw'
  ·exact False.elim (Set.disjoint_left.mp (RelCWComplex.disjoint_openCell_of_ne
    (show (⟨m,i⟩:Σ k,Cell C k) ≠ ⟨m,j⟩ by simpa using hij))
    ⟨z.val,hz',rfl⟩ ⟨w.val,hw',he.symm⟩)
 quotient:=C8 C m hd
end EilenbergGanea.CWSubspace
namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover
variable {X:Type*} [TopologicalSpace X] [T2Space X] (C:Set X) [CWComplex C]
theorem cp1 (hd:∀ k,0 < k -> IsEmpty (Cell C k)):DiscreteTopology C:=by
 apply discreteTopology_iff_forall_isOpen.mpr
 intro U
 apply (wC C).isOpen_preimage.mp
 rw [isOpen_sigma_iff]
 rintro ⟨n,i⟩
 have hn:n=0:=by
  by_contra h
  have:=hd n (Nat.pos_of_ne_zero h)
  exact isEmptyElim i
 subst n
 have:Subsingleton (e8 0):=inferInstance
 exact isOpen_discrete _
end EilenbergGanea.CWSubspace
namespace EilenbergGanea.CWSubspace
open Set Metric Topology CWCover
variable {X:Type*} [TopologicalSpace X] [T2Space X] (C:Set X) [CWComplex C]
def C9 (m:ℕ):lower C m ≃ₜ (CWComplex.skeletonLT C m:Set X) where
 toFun z:=⟨z.val.val,z.property⟩
 invFun z:=⟨⟨z.val,(CWComplex.skeletonLT C m).subset_complex z.property⟩,z.property⟩
 left_inv _:=rfl
 right_inv _:=rfl
 continuous_toFun:=(continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
 continuous_invFun:=(continuous_subtype_val.subtype_mk _).subtype_mk _
theorem Bp:DiscreteTopology (lower C 1):=by
 let S:=CWComplex.skeletonLT C (1:ℕ)
 have hd (k:ℕ) (hk:0 < k):IsEmpty (Cell (S:Set X) k):=by
  refine ⟨fun i=>?_⟩
  have hki:(k:ℕ∞) < 1:=by
   have hi:=i.property
   simpa only [S,CWComplex.skeletonLT_I,Set.mem_ofPred_eq,Nat.cast_one] using hi
  have hkn:k < 1:=by exact_mod_cast hki
  omega
 let:DiscreteTopology (CWComplex.skeletonLT C (1:ℕ):Set X):=by
  exact cp1 (S:Set X) hd
 exact (C9 C 1).symm.discreteTopology
end EilenbergGanea.CWSubspace
namespace EilenbergGanea.CWCollar
open Set Topology CWCover
variable {X:Type*} [TopologicalSpace X] [T2Space X] [CWComplex (univ:Set X)]
def Cz (m:ℕ) (hd:∀ k,m < k -> IsEmpty (Cell (X:=X) k)) :
    Attachment X (Cell (X:=X) m) m:=by
  let a:=CWSubspace.zO (univ:Set X) m hd
  let e:=Homeomorph.Set.univ X
  let L:Set X:=CWComplex.skeletonLT (univ:Set X) m
  let l:a.lower ≃ₜ L:=e.sets rfl
  refine { lower:=L,ck1:=(CWComplex.skeletonLT (univ:Set X) m).closed',
           l0:=characteristic,boundary:=a.boundary,interior:=a.interior,
           disjoint:=fun i j z w hz hw he=>a.disjoint i j z w hz hw (Subtype.ext he),
           quotient:=?_ }
  let g:=l.symm.sumCongr (Homeomorph.refl (Σ _:Cell (X:=X) m,e8 m))
  have h:=e.isQuotientMap.comp (a.quotient.comp g.isQuotientMap)
  convert h using 1
  funext s
  cases s <;> rfl
end EilenbergGanea.CWCollar
namespace EilenbergGanea.ForestCover
open Set Topology CWSubspace
variable {X:Type*} [TopologicalSpace X] [T2Space X] (C:Set X) [CWComplex C]
theorem ZD (hd:∀ k,1 < k -> IsEmpty (Cell C k))
  {r:C} (q:∀ x,Path r x):IsFreeGroup (FundamentalGroup C r):=by
 let:DiscreteTopology (CWSubspace.zO C 1 hd).lower:=Bp C
 exact Zv (CWSubspace.zO C 1 hd) q
end EilenbergGanea.ForestCover
end
noncomputable section
open Classical Set Metric Topology
open Set Topology
open scoped unitInterval
namespace EilenbergGanea.CWCover
variable {X E:Type*} [TopologicalSpace X] [TopologicalSpace E]
variable [CWComplex (univ:Set X)] {p:E -> X} (cov:IsCoveringMap p)
variable [ContractibleSpace E] (hs:Function.Surjective p)
def oY {n:ℕ} (i:Cell (X:=X) n):b3 (p:=p) n:=
 ⟨i,⟨(hs (characteristic i (jB n))).choose,
  (hs (characteristic i (jB n))).choose_spec⟩⟩
end EilenbergGanea.CWCover
namespace EilenbergGanea.CWCollar.Attachment
open Set Topology CWCover PathTransport CubicalSingular
variable {X J:Type*} [TopologicalSpace X] (a:Attachment X J 2)
theorem wR [PathConnectedSpace X]:PathConnectedSpace a.outer:=by
 classical
 let out (j:J) (t:c7 2):a.outer:=⟨_,(a.cZ ⟨j,t⟩).property.1⟩
 let b:c7 2:=Classical.choice inferInstance
 letI:TopologicalSpace J:=⊥
 letI:DiscreteTopology J:=⟨rfl⟩
 let idx:C(a.inner,J):=⟨fun z=>(a.j6.symm z).1,
  (continuous_sigma (fun _=>continuous_const)).comp a.j6.symm.continuous⟩
 have cover (x:X):x ∈ a.outer ∪ a.inner:=by rw [a.k7]; trivial
 let sel (x:X):a.outer:=if h:x ∈ a.outer then ⟨x,h⟩ else out (idx ⟨x,(cover x).resolve_left h⟩) b
 let L (x:X):=ZerothHomotopy.mk (sel x)
 have left (x:a.outer):L x.val=ZerothHomotopy.mk x:=by simp only [L,sel,dif_pos x.property]
 have right (x:a.inner):L x.val=ZerothHomotopy.mk (out (idx x) b):=by
  by_cases h:x.val ∈ a.outer
  ·obtain ⟨⟨j,t⟩,he⟩:=a.cZ.surjective (⟨x.val,h,x.property⟩:(a.outer ∩ a.inner:Set X))
   have hx:a.j6 ⟨j,t.val⟩=x:=Subtype.ext (congrArg (fun w:(a.outer ∩ a.inner:Set X)=>w.val) he)
   have hi:idx x=j:=by rw [←hx]; exact congrArg Sigma.fst (a.j6.symm_apply_apply _)
   rw [hi,←show (out j t).val=x.val from congrArg (fun w:(a.outer ∩ a.inner:Set X)=>w.val) he,left]
   exact ZerothHomotopy.sound ((PathConnectedSpace.joined t b).somePath.map
    ((continuous_subtype_val.comp (a.cZ.continuous.comp continuous_sigmaMk)).subtype_mk _))
  ·simp only [L,sel,dif_neg h]
 refine ⟨⟨sel (Classical.choice inferInstance)⟩,fun x y=>@Quotient.exact _ (pathSetoid a.outer) x y ?_⟩
 change ZerothHomotopy.mk x=ZerothHomotopy.mk y
 rw [←left x,←left y]
 let p:Path x.val y.val:=(PathConnectedSpace.joined _ _).somePath
 letI:LocallyPathConnectedSpace I:=(isQuotientMap_projIcc (h:=zero_le_one (α:=ℝ))).locallyPathConnectedSpace
 have lc:IsLocallyConstant (fun t=>L (p t)):=by
  apply (IsLocallyConstant.iff_eventually_eq _).2
  intro t
  have patch (W:Set X) (ho:IsOpen W) (ht:p t ∈ W)
    (same:∀ z w:W,Joined z w → L z.val=L w.val):∀ᶠ s in 𝓝 t,L (p s)=L (p t):=by
   filter_upwards [pathComponentIn_mem_nhds ((ho.preimage p.continuous).mem_nhds ht)] with s hs
   change JoinedIn (p ⁻¹' W) t s at hs
   let f:(p ⁻¹' W) → W:=fun z=>⟨p z,z.property⟩
   exact (same _ _ (hs.joined_subtype.map (show Continuous f from
    (p.continuous.comp continuous_subtype_val).subtype_mk _))).symm
  rcases cover (p t) with ht|ht
  ·exact patch _ a.Gm ht fun z w h=>(left z).trans ((ZerothHomotopy.sound h.somePath).trans (left w).symm)
  ·apply patch _ a.Gp ht
   intro z w h
   rw [right z,right w]
   have eq:=(@inferInstance (PreconnectedSpace I)).constant (idx.continuous.comp h.somePath.continuous) (x:=0) (y:=1)
   simpa only [Function.comp_apply,Path.source,Path.target] using congrArg (fun j=>ZerothHomotopy.mk (out j b)) eq
 simpa only [p.source,p.target] using lc.apply_eq_of_preconnectedSpace 0 1
end EilenbergGanea.CWCollar.Attachment
namespace EilenbergGanea.CWCollar
open Set Metric Topology CWCover
universe u
variable {X E:Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ:Set X)] {p:E -> X} (cov:IsCoveringMap p)
variable {m:ℕ} (hd:∀ k,m < k -> IsEmpty (Cell (X:=X) k))
abbrev d9:=Cz m hd
omit [T2Space X] [CWComplex (univ:Set X)] in
private theorem Ed {D F:Type*} [TopologicalSpace D] [TopologicalSpace F]
  {q:D → X} {f:F → E} {g:F → D} (hq:IsQuotientMap q)
  (hp:IsLocalHomeomorph p) (hf:Continuous f) (hg:IsOpenMap g)
  (comm:∀ t,p (f t) = q (g t))
  (lift:∀ d e,p e = q d → ∃ t,g t = d ∧ f t = e):IsQuotientMap f:=by
 constructor
 ·apply isCoinducing_iff.mpr
  intro A
  refine ⟨fun h=>isOpen_iff_mem_nhds.mpr fun e he=>?_,fun h=>h.preimage hf⟩
  obtain ⟨U,hU,hu,inj⟩:=hp.isLocallyInjective e
  have eq:q ⁻¹' (p '' (U ∩ A)) = g '' (f ⁻¹' U ∩ f ⁻¹' A):=by
   ext d
   constructor
   ·rintro ⟨x,hx,hp'⟩
    obtain ⟨t,rfl,rfl⟩:=lift d x hp'
    exact ⟨t,hx,rfl⟩
   ·rintro ⟨t,ht,rfl⟩
    exact ⟨f t,ht,comm t⟩
  have ho:=hq.isOpen_preimage.mp (eq.symm ▸ hg _ ((hU.preimage hf).inter h))
  apply Filter.mem_of_superset ((hU.inter (ho.preimage hp.continuous)).mem_nhds
   (show e ∈ U ∩ p ⁻¹' (p '' (U ∩ A)) from ⟨hu,e,⟨hu,he⟩,rfl⟩))
  rintro x ⟨hx,y,hy,hxy⟩
  exact inj hy.1 hx hxy ▸ hy.2
 ·intro e
  obtain ⟨d,hd⟩:=hq.surjective (p e)
  obtain ⟨t,_,ht⟩:=lift d e hd.symm
  exact ⟨t,ht⟩
def d5:Attachment E (b3 (p:=p) m) m where
 lower:=p ⁻¹' (d9 hd).lower
 ck1:=(d9 hd).ck1.preimage cov.continuous
 l0:=i7 cov
 boundary:=by
  intro c z hz
  change p (i7 cov c z) ∈ (d9 hd).lower
  rw [b9 cov c z]
  exact (d9 hd).boundary c.1 z hz
 interior:=by
  intro c z hz
  change p (i7 cov c z) ∉ (d9 hd).lower
  rw [b9 cov c z]
  exact (d9 hd).interior c.1 z hz
 disjoint:=by
  intro c d z w hz hw he
  have h:=congrArg p he
  rw [b9 cov c z,b9 cov d w] at h
  obtain ⟨hi,rfl⟩:=(d9 hd).disjoint c.1 d.1 z w hz hw h
  exact ⟨WM cov hi z he,rfl⟩
 quotient:=by
  let g:(p ⁻¹' (d9 hd).lower ⊕ (Σ _:b3 (p:=p) m,e8 m)) → (d9 hd).Rep:=Sum.map ((d9 hd).lower.restrictPreimage p)
   (Sigma.map (fun c:b3 (p:=p) m=>c.1) (fun _=>id (α:=e8 m)))
  apply Ed (g:=g) (d9 hd).quotient cov.isLocalHomeomorph
   (continuous_subtype_val.sumElim (continuous_sigma fun c=>(i7 cov c).continuous))
   ((cov.isLocalHomeomorph.isOpenMap.restrictPreimage _).sumMap
    (isOpenMap_sigma_map.mpr fun _=>IsOpenMap.id))
  ·rintro (x|⟨c,z⟩)
   ·rfl
   ·exact b9 cov c z
  ·rintro (x|⟨i,z⟩) e h
   ·exact ⟨.inl ⟨e,show p e ∈ (d9 hd).lower from h.symm ▸ x.property⟩,
     congrArg Sum.inl (Subtype.ext h),rfl⟩
   ·obtain ⟨c,hc,he⟩:=u0 cov i z e h
    subst i
    exact ⟨.inr ⟨c,z⟩,rfl,he⟩
theorem z4 (e:E) :
  (d5 cov hd).radius e=(d9 hd).radius (p e):=by
 obtain ⟨r,rfl⟩:=(d5 cov hd).quotient.surjective e
 rcases r with x | ⟨c,z⟩
 ·exact ((d5 cov hd).MJ x).trans ((d9 hd).MJ ⟨p x.val,x.property⟩).symm
 ·change (d5 cov hd).radius ((d5 cov hd).l0 c z)=(d9 hd).radius (p (i7 cov c z))
  rw [(d5 cov hd).j7,b9 cov c z]
  exact ((d9 hd).j7 c.1 z).symm
@[simp] theorem ZE:(d5 cov hd).outer=p ⁻¹' (d9 hd).outer:=by
 ext e
 change 0 < (d5 cov hd).radius e ↔ 0 < (d9 hd).radius (p e)
 rw [z4 cov hd e]
@[simp] theorem dv5:(d5 cov hd).inner=p ⁻¹' (d9 hd).inner:=by
 ext e
 change (d5 cov hd).radius e < 1 ↔ (d9 hd).radius (p e) < 1
 rw [z4 cov hd e]
def y1:(d5 cov hd).outer ≃ₜ p ⁻¹' (d9 hd).outer:=
 Homeomorph.setCongr (ZE cov hd)
def kR:C((d5 cov hd).outer,(d9 hd).outer):=
 (⟨(d9 hd).outer.restrictPreimage p,
  (cov.continuous.comp continuous_subtype_val).subtype_mk _⟩ :
  C(p ⁻¹' (d9 hd).outer,(d9 hd).outer)).comp
   (y1 cov hd:C(_,_))
theorem ZF (c:b3 (p:=p) m) (z:c7 m) :
  p ((d5 cov hd).cZ ⟨c,z⟩).val =
   ((d9 hd).cZ ⟨c.1,z⟩).val:=by
 exact b9 cov c z.val.val
end EilenbergGanea.CWCollar
open Classical Set
namespace EilenbergGanea.CoverKernel
variable {X E:Type*} [TopologicalSpace X] [TopologicalSpace E]
variable {p:E -> X} (cov:IsCoveringMap p) (U:Set X)
def projection:C(p ⁻¹' U,U):=⟨U.restrictPreimage p,(cov.continuous.comp continuous_subtype_val).subtype_mk _⟩
def inclusion:C(U,X):=⟨Subtype.val,continuous_subtype_val⟩
theorem ZG {e:E} (γ:Path (p e) (p e))
  (h:γ.Homotopic (Path.refl (p e))):cov.liftPath γ e γ.source 1=e:=by
 have he:=cov.liftPath_apply_one_eq_of_homotopicRel h e γ.source rfl
 change cov.liftPath γ e γ.source 1=cov.liftPath (ContinuousMap.const _ (p e)) e rfl 1 at he
 rw [cov.liftPath_const (e:=e) rfl] at he
 exact he
variable (e:p ⁻¹' U)
def QY:(FundamentalGroup (p ⁻¹' U) e)ᵐᵒᵖ →* (FundamentalGroup U (projection cov U e))ᵐᵒᵖ:=
 (FundamentalGroup.map (projection cov U) e).op
def kS:(FundamentalGroup U (projection cov U e))ᵐᵒᵖ →* (FundamentalGroup X (p e.val))ᵐᵒᵖ:=
 (FundamentalGroup.map (inclusion U) (projection cov U e)).op
theorem ZH:Function.Injective (QY cov U e):=by
 intro a b he
 apply MulOpposite.unop_injective
 exact (cov.restrictPreimage U).injective_path_homotopic_map e e (congrArg MulOpposite.unop he)
theorem ZI [SimplyConnectedSpace E]:(QY cov U e).range=(kS cov U e).ker:=by
 apply le_antisymm
 ·rintro _ ⟨v,rfl⟩
  let f:C(E,X):=⟨p,cov.continuous⟩
  have h:=Subsingleton.elim (FundamentalGroup.map (inclusion (p ⁻¹' U)) e v.unop) 1
  apply MulOpposite.unop_injective
  obtain ⟨γ,hγ⟩:=Quotient.exists_rep v.unop
  change FundamentalGroup.map _ _ (FundamentalGroup.map _ _ v.unop) = 1
  rw [← hγ] at h ⊢
  exact (congrArg (FundamentalGroup.map f e.val) h).trans (map_one _)
 ·rintro w hw
  obtain ⟨γ,hγ⟩:=Quotient.exists_rep w.unop
  have he:MulOpposite.op (Path.Homotopic.Quotient.mk γ) = w:=congrArg MulOpposite.op hγ
  subst w
  let q:=γ.map (inclusion U).continuous
  let t:=cov.liftPath q e.val q.source
  have lift (s):p (t s) = (γ s).val:=congrFun (cov.liftPath_lifts q e.val q.source) s
  let δ:Path e e:=⟨⟨fun s=>⟨t s,show p (t s) ∈ U from (lift s).symm ▸ (γ s).property⟩,t.continuous.subtype_mk _⟩,
   Subtype.ext (cov.liftPath_zero ..),Subtype.ext (ZG cov q
    (Path.Homotopic.Quotient.eq.mp (congrArg MulOpposite.unop hw)))⟩
  refine ⟨MulOpposite.op (Path.Homotopic.Quotient.mk δ),?_⟩
  exact congrArg (fun r=>MulOpposite.op (Path.Homotopic.Quotient.mk r))
   (Path.ext (funext fun s=>Subtype.ext (lift s)):δ.map (projection cov U).continuous = γ)
def ZJ [SimplyConnectedSpace E] :
  (FundamentalGroup (p ⁻¹' U) e)ᵐᵒᵖ ≃* (kS cov U e).ker:=
 (MonoidHom.ofInjective (ZH cov U e)).trans
  (MulEquiv.subgroupCongr (ZI cov U e))
end EilenbergGanea.CoverKernel
namespace EilenbergGanea.PathTransport
variable {X Y:Type*} [TopologicalSpace X] [TopologicalSpace Y]
def Db {r x:X} (q:Path r x) (p:Path x x):(FundamentalGroup X r)ᵐᵒᵖ:=
 MulOpposite.op (bR ((q.trans p).trans q.symm))
def M8 {r x:X} (q s:Path r x):(FundamentalGroup X r)ᵐᵒᵖ:=
 MulOpposite.op (bR (q.trans s.symm))
@[simp] theorem ZK (f:C(X,Y)) {r x:X} (q:Path r x) (p:Path x x) :
  (FundamentalGroup.map f r).op (Db q p)=Db (q.map f.continuous) (p.map f.continuous):=by
 apply MulOpposite.unop_injective
 change bR (((q.trans p).trans q.symm).map f.continuous)=_
 rw [Path.map_trans,Path.map_trans,<- Path.map_symm]
 rfl
theorem QZ {r x:X} (q s:Path r x) (p:Path x x) :
    Db q p=M8 q s * Db s p * (M8 q s)⁻¹:=by
  apply MulOpposite.unop_injective
  change bR ((q.trans p).trans q.symm) =
    ((bR (q.trans s.symm)).trans (bR ((s.trans p).trans s.symm))).trans (bR (q.trans s.symm)).symm
  rw [show (bR (q.trans s.symm)).symm=bR (s.trans q.symm) by
    rw [bR,<- Path.Homotopic.Quotient.mk_symm,Path.trans_symm,Path.symm_symm]]
  simp only [bR,Path.Homotopic.Quotient.mk_trans,Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_assoc]
  rw [<- Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk s).symm (Path.Homotopic.Quotient.mk s),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]
  rw [<- Path.Homotopic.Quotient.trans_assoc (Path.Homotopic.Quotient.mk s).symm (Path.Homotopic.Quotient.mk s),
    Path.Homotopic.Quotient.symm_trans,Path.Homotopic.Quotient.refl_trans]
theorem ZL {r x y:X} (q:Path r x) (s:Path r y)
  (p:Path x x) (t:Path y y) (hqs:∀ z,q z=s z) (hpt:∀ z,p z=t z) :
  Db q p=Db s t:=by
 have hxy:x=y:=by simpa using hqs 1
 subst y
 have hq:q=s:=Path.ext (funext hqs)
 have hp:p=t:=Path.ext (funext hpt)
 rw [hq,hp]
end EilenbergGanea.PathTransport
end
noncomputable section
open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff
namespace EilenbergGanea.KernelCycles
open Classical
variable {G A:Type*} [Group G] (a:A -> G)
abbrev Kernel:=(aD a).ker
abbrev JK:=Additive (Abelianization (Kernel a))
def DH:Kernel a →* Multiplicative (cycles a) where
 toFun w:=Multiplicative.ofAdd ⟨aW a w.val 1,by
  change bY a (aW a w.val 1)=0
  rw [mJ,w.property,mul_one,sub_self]⟩
 map_one':=by apply (Equiv.refl _:Multiplicative (cycles a) ≃ cycles a).injective; apply Subtype.ext; exact N9 a 1
 map_mul' w z:=by
  apply (Equiv.refl _:Multiplicative (cycles a) ≃ cycles a).injective
  apply Subtype.ext
  change aW a (w.val*z.val) 1=aW a w.val 1 + aW a z.val 1
  rw [d2,w.property,mul_one]
def k5:JK a →ₗ[ℤ] cycles a:=
 (Abelianization.lift (DH a)).toAdditive.toIntLinearMap
@[simp] theorem ZM (w:Kernel a) :
  (k5 a (Additive.ofMul (Abelianization.of w))).val=aW a w.val 1:=rfl
variable (t:G -> FreeGroup A) (ht:∀ g,aD a (t g)=g)
def bridge (w:FreeGroup A) (g:G):Kernel a:=
 ⟨t g * w * (t (g * aD a w))⁻¹,by
  change aD a (t g * w * (t (g * aD a w))⁻¹)=1
  simp only [map_mul,map_inv,ht]
  group⟩
@[simp] theorem dx1 (g:G):bridge a t ht 1 g=1:=by
 apply Subtype.ext
 simp [bridge]
theorem ZO (w z:FreeGroup A) (g:G) :
  bridge a t ht (w*z) g=bridge a t ht w g * bridge a t ht z (g * aD a w):=by
 apply Subtype.ext
 simp only [bridge,Subgroup.coe_mul,map_mul,mul_assoc]
 group
theorem ZP (w:FreeGroup A) (g:G) :
  bridge a t ht w⁻¹ g=(bridge a t ht w (g * (aD a w)⁻¹))⁻¹:=by
 apply Subtype.ext
 simp only [bridge,Subgroup.coe_inv,map_inv]
 simp only [inv_mul_cancel_right]
 group
def kJ (w:FreeGroup A) (g:G):JK a:=
 Additive.ofMul (Abelianization.of (bridge a t ht w g))
@[simp] theorem du9 (g:G):kJ a t ht 1 g=0:=by simp [kJ]
theorem ZQ (w z:FreeGroup A) (g:G) :
  kJ a t ht (w*z) g=kJ a t ht w g + kJ a t ht z (g * aD a w):=by
 unfold kJ
 rw [ZO,map_mul]
 rfl
theorem dg0 (w:FreeGroup A) (g:G) :
  kJ a t ht w⁻¹ g=-kJ a t ht w (g * (aD a w)⁻¹):=by
 unfold kJ
 rw [ZP,map_inv]
 rfl
def jK:aE G A →ₗ[ℤ] JK a:=
 Finsupp.linearCombination ℤ (fun p=>kJ a t ht (FreeGroup.of p.2) p.1)
@[simp] theorem ZR (g:G) (x:A) (n:ℤ) :
  jK a t ht (Finsupp.single (g,x) n)=n • kJ a t ht (FreeGroup.of x) g:=by
 simp [jK]
theorem ZS (w:FreeGroup A) (g:G) :
  jK a t ht (aW a w g)=kJ a t ht w g:=by
 induction w using FreeGroup.induction_on generalizing g with
 | C1=>simp
 | of x=>simp
 | inv_of x=>rw [f9,map_neg,dg0]; simp
 | mul w z hw hz=>rw [d2,map_add,hw,hz,ZQ]
theorem ZT (w:Kernel a):kJ a t ht w.val 1=Additive.ofMul (Abelianization.of w):=by
 let u:Kernel a:=⟨t 1,ht 1⟩
 have he:bridge a t ht w.val 1=u*w*u⁻¹:=by
  apply Subtype.ext
  change t 1 * w.val * (t (1 * aD a w.val))⁻¹=t 1 * w.val * (t 1)⁻¹
  rw [w.property,mul_one]
 change Additive.ofMul (Abelianization.of (bridge a t ht w.val 1))=_
 apply congrArg Additive.ofMul
 rw [he,map_mul,map_mul,map_inv]
 simp [mul_comm]
theorem ZU (w:JK a) :
  jK a t ht (k5 a w).val=w:=by
 revert w
 change ∀ w:Abelianization (Kernel a),
  jK a t ht (k5 a (Additive.ofMul w)).val=Additive.ofMul w
 intro w
 induction w using QuotientGroup.induction_on with
 | H w=>
  change jK a t ht (k5 a (Additive.ofMul (Abelianization.of w))).val=Additive.ofMul (Abelianization.of w)
  rw [ZM,ZS,ZT]
def anchors:(G →₀ ℤ) →ₗ[ℤ] aE G A:=Finsupp.linearCombination ℤ (fun g=>aW a (t g) 1)
theorem ZV (w:FreeGroup A) (g:G) :
  aW a (bridge a t ht w g).val 1 =
   aW a (t g) 1 + aW a w g - aW a (t (g * aD a w)) 1:=by
 change aW a (t g*w*(t (g*aD a w))⁻¹) 1=_
 rw [d2,d2,f9]
 simp only [ht,map_mul,one_mul,mul_inv_cancel,sub_eq_add_neg]
theorem xG (c:aE G A) :
    (k5 a (jK a t ht c)).val=c - anchors a t (bY a c):=by
  have he:(cycles a).subtype.comp ((k5 a).comp (jK a t ht)) =
      LinearMap.id - (anchors a t).comp (bY a):=by
    apply Finsupp.lhom_ext
    rintro ⟨g,x⟩ n
    simp only [LinearMap.comp_apply,ZR,map_smul,LinearMap.sub_apply,
      LinearMap.id_apply,Od]
    change n • aW a (bridge a t ht (FreeGroup.of x) g).val 1 =
      Finsupp.single (g,x) n - n • anchors a t (Finsupp.single (g*a x) 1 - Finsupp.single g 1)
    rw [ZV]
    simp only [Lq,aD,FreeGroup.lift_apply_of,anchors,map_sub,Finsupp.linearCombination_single,one_smul]
    rw [<- Finsupp.smul_single_one (g,x) n]
    simp only [smul_add,smul_sub]
    abel
  exact LinearMap.congr_fun he c
def Bq:JK a ≃ₗ[ℤ] cycles a:=
 LinearEquiv.ofLinearMap (k5 a) ((jK a t ht).comp (cycles a).subtype)
  (by apply LinearMap.ext; intro c; apply Subtype.ext; exact (xG a t ht c.val).trans (by rw [c.property,map_zero,sub_zero]; rfl))
  (by apply LinearMap.ext; intro w; exact ZU a t ht w)
end EilenbergGanea.KernelCycles
namespace EilenbergGanea.ax4
open Classical
universe u
variable {H:Type u} {G R:Type*} [Group H] [Group G]
variable (φ:H →* G) (hf:Function.Surjective φ)
variable (r:R -> H) (hr:∀ j,φ (r j)=1)
include hf in
theorem ZW [IsFreeGroup H]
    (hp:φ.ker=Subgroup.normalClosure (Set.range r))
    (B:aE G R ≃ₗ[ℤ] Additive (Abelianization φ.ker))
    (hB:∀ g j,∃ k:H,φ k=g /\ B (Finsupp.single (g,j) 1) =
      Additive.ofMul (Abelianization.of (⟨k*r j*k⁻¹,by
        change φ (k*r j*k⁻¹)=1
        rw [map_mul,map_mul,map_inv,hr,mul_one,mul_inv_cancel]⟩:φ.ker)))
    {K:Type*} [Group K] (χ:G ≃* K) :
    ∃ (A:Type u) (a:A -> K),Function.Surjective (aD a) /\
      ∃ (s:R -> FreeGroup A),(∀ j,aD a (s j)=1) /\
        (aD a).ker=Subgroup.normalClosure (Set.range s) /\
        ∃ E:aE K R ≃ₗ[ℤ] cycles a,
          ∀ c,(E c:aE K A)=aO a s c:=by
  let A:=IsFreeGroup.Generators H
  let e:FreeGroup A ≃* H:=IsFreeGroup.mulEquiv H
  let a:A → K:=fun x=>χ (φ (e (FreeGroup.of x)))
  have ha:aD a=χ.toMonoidHom.comp (φ.comp e.toMonoidHom):=by
    apply FreeGroup.ext_hom
    intro x
    simp [aD,a]
  have back (k:H):aD a (e.symm k)=χ (φ k):=by simp [ha]
  have hker (w:FreeGroup A):w ∈ (aD a).ker ↔ e w ∈ φ.ker:=by
    change aD a w=1 ↔ φ (e w)=1
    rw [ha]; exact χ.map_eq_one_iff
  have hsur:Function.Surjective (aD a):=by rw [ha]; exact χ.surjective.comp (hf.comp e.surjective)
  let s:=fun j=>e.symm (r j)
  have hs (j):aD a (s j)=1:=by simp [s,back,hr]
  have hn:(aD a).ker=Subgroup.normalClosure (Set.range s):=by
    rw [show Set.range s=e.symm.toMonoidHom '' Set.range r from Set.range_comp _ _,
      ← Subgroup.map_normalClosure _ _ e.symm.surjective,← hp]
    ext w
    rw [hker]
    exact ⟨fun h=>⟨e w,h,e.symm_apply_apply w⟩,by rintro ⟨v,h,rfl⟩; simpa using h⟩
  let ke:φ.ker ≃* (aD a).ker:=
    { toFun:=fun k=>⟨e.symm k.val,(hker _).2 (by simpa using k.property)⟩
      invFun:=fun k=>⟨e k.val,(hker _).1 k.property⟩
      left_inv:=fun k=>Subtype.ext (e.apply_symm_apply k.val)
      right_inv:=fun k=>Subtype.ext (e.symm_apply_apply k.val)
      map_mul':=fun k l=>Subtype.ext (map_mul e.symm _ _) }
  let t:=fun g=>(hsur g).choose
  let C:=KernelCycles.Bq a t (fun g=>(hsur g).choose_spec)
  let D:aE K R ≃ₗ[ℤ] aE G R:=Finsupp.domLCongr (Equiv.prodCongr χ.symm.toEquiv (Equiv.refl R))
  let E:aE K R ≃ₗ[ℤ] cycles a :=D.trans (B.trans (ke.abelianizationCongr.toAdditive.toIntLinearEquiv.trans C))
  refine ⟨A,a,hsur,s,hs,hn,E,?_⟩
  have he:(cycles a).subtype.comp E.toLinearMap=aO a s:=by
    apply Finsupp.lhom_ext
    rintro ⟨g,j⟩ n
    rw [← Finsupp.smul_single_one (g,j) n,map_smul,map_smul]
    congr 1
    obtain ⟨k,hk,hkj⟩:=hB (χ.symm g) j
    change (E (Finsupp.single (g,j) 1)).val=_
    simp only [E,D,LinearEquiv.trans_apply,Finsupp.domLCongr_single]
    change (C (ke.abelianizationCongr.toAdditive.toIntLinearEquiv (B (Finsupp.single (χ.symm g,j) 1)))).val=_
    rw [hkj]
    change aW a (e.symm (k*r j*k⁻¹)) 1=aO a s (Finsupp.single (g,j) 1)
    rw [map_mul,map_mul,map_inv,n5 a _ _ (hs j),one_mul,back,hk,χ.apply_symm_apply,f1,one_smul]
  exact LinearMap.congr_fun he
end EilenbergGanea.ax4
end
noncomputable section
open Classical Set Metric Topology
namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular
open scoped ContinuousMap
universe u
variable {X E:Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ:Set X)] {p:E -> X}
variable (cov:IsCoveringMap p) (hd:∀ k,2 < k -> IsEmpty (Cell (X:=X) k))
abbrev base:=d9 hd
abbrev g0:=d5 cov hd
instance dp5 [PathConnectedSpace X]:PathConnectedSpace (base hd).outer:=
 (base hd).wR
instance dm9 [PathConnectedSpace E]:PathConnectedSpace (g0 cov hd).outer:=
 (g0 cov hd).wR
theorem Fe [PathConnectedSpace X] (r:(base hd).outer) :
  IsFreeGroup (FundamentalGroup (base hd).outer r):=by
 let a:=base hd
 let S:=CWComplex.skeletonLT (univ:Set X) (2:ℕ)
 have hs (k:ℕ) (hk:1 < k):IsEmpty (CWSubspace.Cell (S:Set X) k):=by
  refine ⟨fun i=>?_⟩
  have hi:(k:ℕ∞) < 2:=by
   simpa only [S,CWComplex.skeletonLT_I,Set.mem_ofPred_eq,Nat.cast_ofNat] using i.property
  have hki:k < 2:=by exact_mod_cast hi
  omega
 have hr:Function.Surjective a.l7:=fun x=>⟨a.lB x,a.QG x⟩
 let:PathConnectedSpace a.lower:=hr.pathConnectedSpace a.l7.continuous
 let:PathConnectedSpace (S:Set X):=inferInstanceAs (PathConnectedSpace a.lower)
 let:IsFreeGroup (FundamentalGroup a.lower (a.l7 r)):=
  ForestCover.ZD (S:Set X) hs (fun y=>(PathConnectedSpace.joined _ y).somePath)
 let e:a.outer ≃ₕ a.lower:=
  ⟨a.l7,a.lB,⟨a.yI.symm⟩,by
   have he:a.l7.comp a.lB=ContinuousMap.id a.lower:=ContinuousMap.ext a.QG
   rw [he]⟩
 exact IsFreeGroup.ofMulEquiv (lT e r).symm
variable [ContractibleSpace E]
variable (e:(g0 cov hd).outer)
abbrev root:(base hd).outer:=kR cov hd e
abbrev kS:(FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ →*
  (FundamentalGroup X (p e.val))ᵐᵒᵖ:=
 (FundamentalGroup.map (CoverKernel.inclusion (base hd).outer) (root cov hd e)).op
abbrev Q7:(FundamentalGroup (g0 cov hd).outer e)ᵐᵒᵖ →*
  (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ:=
 (FundamentalGroup.map (kR cov hd) e).op
def mO:(FundamentalGroup (g0 cov hd).outer e)ᵐᵒᵖ ≃* (kS cov hd e).ker:=
 (lT (y1 cov hd).toHomotopyEquiv e).op.trans
  (CoverKernel.ZJ cov (base hd).outer (y1 cov hd e))
@[simp] theorem Q8 (w:(FundamentalGroup (g0 cov hd).outer e)ᵐᵒᵖ) :
  (mO cov hd e w).val=Q7 cov hd e w:=by
 obtain ⟨γ,hγ⟩:=Quotient.exists_rep w.unop
 have he:MulOpposite.op (bR γ)=w:=congrArg MulOpposite.op hγ
 rw [<- he]
 rfl
variable (q:∀ y:(g0 cov hd).outer,Path e y) (y₀:c7 2)
def xO:(b3 (p:=p) 2 →₀ ℤ) ≃ₗ[ℤ]
  Additive (Abelianization (kS cov hd e).ker):=
 ((g0 cov hd).wB y₀).trans ((sI q).trans
  (mO cov hd e).abelianizationCongr.toAdditive.toIntLinearEquiv)
theorem Z1 (c:b3 (p:=p) 2) :
  xO cov hd e q y₀ (Finsupp.single c 1) =
   Additive.ofMul (Abelianization.of (mO cov hd e
    ((g0 cov hd).kH q y₀ c))):=by
 simp only [xO,LinearEquiv.trans_apply]
 rw [Attachment.Zn,QJ]
 rfl
end EilenbergGanea.CWPresentation
namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular
open scoped ContinuousMap
universe u
variable {X E:Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ:Set X)] {p:E -> X}
variable (cov:IsCoveringMap p) (hd:∀ k,2 < k -> IsEmpty (Cell (X:=X) k))
variable [ContractibleSpace E] (e:(g0 cov hd).outer)
variable (q:∀ y:(g0 cov hd).outer,Path e y) (y₀:c7 2)
omit [ContractibleSpace E] in
@[simp] theorem Ra (c:b3 (p:=p) 2) (z:c7 2) :
  kR cov hd ((g0 cov hd).g3 c z)=(base hd).g3 c.1 z:=
 Subtype.ext (ZF cov hd c z)
def mD (c:b3 (p:=p) 2) :
  Path (root cov hd e) ((base hd).g3 c.1 y₀):=
 ((q ((g0 cov hd).g3 c y₀)).map (kR cov hd).continuous).cast rfl
  (Ra cov hd c y₀).symm
def wD (c:b3 (p:=p) 2) :
  (FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ:=
 Db (mD cov hd e q y₀ c)
  ((d3 y₀).map ((base hd).g3 c.1).continuous)
omit [ContractibleSpace E] in
theorem Rb (c:b3 (p:=p) 2) :
  Q7 cov hd e ((g0 cov hd).kH q y₀ c) =
   wD cov hd e q y₀ c:=by
 change (FundamentalGroup.map (kR cov hd) e).op
  (Db (q ((g0 cov hd).g3 c y₀))
   ((d3 y₀).map ((g0 cov hd).g3 c).continuous))=_
 rw [ZK]
 apply ZL
 ·intro t; rfl
 ·intro t; exact Ra cov hd c (d3 y₀ t)
variable (hs:Function.Surjective p)
def relator (j:Cell (X:=X) 2):=wD cov hd e q y₀ (oY hs j)
@[simp] theorem Nb (j:Cell (X:=X) 2):kS cov hd e (relator cov hd e q y₀ hs j)=1:=by
 rw [relator,<- Rb,<- Q8]
 exact (mO cov hd e ((g0 cov hd).kH q y₀ (oY hs j))).property
variable [PathConnectedSpace X]
theorem bz0:(kS cov hd e).ker =
  Subgroup.normalClosure (Set.range (relator cov hd e q y₀ hs)):=by
 let bq:∀ y:(base hd).outer,Path (root cov hd e) y:=fun y=>(PathConnectedSpace.joined _ y).somePath
 have hn:=(base hd).Zi bq y₀ (ForestCover.QX (base hd))
 apply le_antisymm
 ·rw [show (kS cov hd e).ker=Subgroup.normalClosure (Set.range ((base hd).kH bq y₀)) from hn]
  apply Subgroup.normalClosure_le_normal
  rintro w ⟨j,rfl⟩
  let s:Path (root cov hd e) ((base hd).g3 j y₀):=mD cov hd e q y₀ (oY hs j)
  change Db (bq ((base hd).g3 j y₀)) ((d3 y₀).map ((base hd).g3 j).continuous) ∈ _
  rw [QZ (bq ((base hd).g3 j y₀)) s]
  exact (inferInstance:(Subgroup.normalClosure (Set.range (relator cov hd e q y₀ hs))).Normal).conj_mem _ (Subgroup.subset_normalClosure ⟨j,rfl⟩) _
 ·apply Subgroup.normalClosure_le_normal
  rintro w ⟨j,rfl⟩
  exact Nb cov hd e q y₀ hs j
end EilenbergGanea.CWPresentation
namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular
open scoped ContinuousMap
universe u
variable {X E:Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ:Set X)] {p:E -> X}
variable (cov:IsCoveringMap p) (hd:∀ k,2 < k -> IsEmpty (Cell (X:=X) k))
variable [ContractibleSpace E] (e:(g0 cov hd).outer)
variable (q:∀ y:(g0 cov hd).outer,Path e y) (y₀:c7 2) (hs:Function.Surjective p)
open Path.Homotopic.Quotient
private theorem Gt (a:E) {x:X} (γ:PQ (p a) x) (z:p ⁻¹' {x})
  (s:PQ a z.val):cov.monodromy γ ⟨a,rfl⟩ = z ↔
   s.map ⟨p,cov.continuous⟩ = γ.cast rfl z.property:=by
 constructor
 ·rintro rfl
  rw [Subsingleton.elim s (cov.liftPathQuotient γ ⟨a,rfl⟩)]
  exact cov.map_liftPathQuotient γ ⟨a,rfl⟩
 ·exact cov.monodromy_eq_of_map_eq (ex:=⟨a,rfl⟩) (ey:=z) s
private def endpoint (a:E) (x:X):PQ (p a) x ≃ p ⁻¹' {x}:=
 Equiv.ofBijective (fun γ=>cov.monodromy γ ⟨a,rfl⟩) (by
  constructor
  ·intro γ δ h
   let z:=cov.monodromy δ ⟨a,rfl⟩
   let s:=cov.liftPathQuotient δ ⟨a,rfl⟩
   have hh:=((Gt cov a γ z s).mp h).symm.trans ((Gt cov a δ z s).mp rfl)
   exact eq_of_heq ((Path.Homotopic.Quotient.cast_heq rfl z.property).symm.trans ((heq_of_eq hh).trans (Path.Homotopic.Quotient.cast_heq rfl z.property)))
  ·rintro ⟨z,rfl⟩
   let s:=bR (PathConnectedSpace.joined a z).somePath
   exact ⟨s.map ⟨p,cov.continuous⟩,cov.monodromy_map s⟩)
private def mark (j:Cell (X:=X) 2) :
  (p ⁻¹' {characteristic j (jB 2)}) ≃ p ⁻¹' {characteristic j y₀.val.val}:=
 Equiv.ofBijective (fun z=>⟨i7 cov ⟨j,z⟩ y₀.val.val,b9 cov ⟨j,z⟩ _⟩) (by
  let r:=(PathConnectedSpace.joined (jB 2) y₀.val.val).somePath
  convert cov.monodromy_bijective (bR (r.map (characteristic j).continuous)) using 1
  funext z
  symm
  apply cov.monodromy_eq_of_map_eq (bR (r.map (i7 cov ⟨j,z⟩).continuous) |>.cast (u6 cov ⟨j,z⟩).symm rfl)
  apply congrArg Path.Homotopic.Quotient.mk
  exact Path.ext (funext fun t=>b9 cov ⟨j,z⟩ (r t)))
private def sP (c:b3 (p:=p) 2):=
 bR ((mD cov hd e q y₀ c).map continuous_subtype_val)
private theorem I8 {Y:Type*} [TopologicalSpace Y] {a b:Y} (s t:Path a b) (f:C(Y,X)) :
  bR ((s.trans t.symm).map f.continuous) = (bR (s.map f.continuous)).trans (bR (t.map f.continuous)).symm:=by
 rw [Path.map_trans,← Path.map_symm]; rfl
private def shift {x y:X} (t:PQ x y):(FundamentalGroup X x)ᵐᵒᵖ ≃ PQ x y where
 toFun g:=g.unop.trans t
 invFun s:=MulOpposite.op (s.trans t.symm)
 left_inv g:=congrArg MulOpposite.op (by simp; rfl)
 right_inv s:=by change (s.trans t.symm).trans t=s; simp
private def JL (j:Cell (X:=X) 2):(FundamentalGroup X (p e.val))ᵐᵒᵖ ≃
  p ⁻¹' {characteristic j (jB 2)}:=
 let t:=sP cov hd e q y₀ (oY hs j)
 ((shift t).trans (endpoint cov e.val _)).trans (mark cov y₀ j).symm
def wI:(FundamentalGroup X (p e.val))ᵐᵒᵖ × Cell (X:=X) 2 ≃ b3 (p:=p) 2:=
 ((Equiv.prodComm _ _).trans (Equiv.sigmaEquivProd _ _).symm).trans
  (Equiv.sigmaCongrRight (JL cov hd e q y₀ hs))
def rT:(((FundamentalGroup X (p e.val))ᵐᵒᵖ × Cell (X:=X) 2) →₀ ℤ) ≃ₗ[ℤ]
  Additive (Abelianization (kS cov hd e).ker):=
 (Finsupp.domLCongr (wI cov hd e q y₀ hs)).trans (xO cov hd e q y₀)
theorem bx3 (g:(FundamentalGroup X (p e.val))ᵐᵒᵖ) (j:Cell (X:=X) 2) :
  ∃ k:(FundamentalGroup (base hd).outer (root cov hd e))ᵐᵒᵖ,
   kS cov hd e k=g /\
   rT cov hd e q y₀ hs (Finsupp.single (g,j) 1) =
    Additive.ofMul (Abelianization.of (⟨k * relator cov hd e q y₀ hs j * k⁻¹,by
     change kS cov hd e (k * relator cov hd e q y₀ hs j * k⁻¹)=1
     rw [map_mul,map_mul,map_inv,Nb,mul_one,mul_inv_cancel]⟩:(kS cov hd e).ker)):=by
 let c:=wI cov hd e q y₀ hs (g,j)
 let k:=M8 (mD cov hd e q y₀ c) (mD cov hd e q y₀ (oY hs j))
 refine ⟨k,?_,?_⟩
 ·let t:=sP cov hd e q y₀ (oY hs j)
  let s:=bR ((q ((g0 cov hd).g3 c y₀)).map continuous_subtype_val)
  have h:cov.monodromy (g.unop.trans t) ⟨e.val,rfl⟩ = mark cov y₀ j c.2:=
   ((mark cov y₀ j).apply_symm_apply _).symm
  have ha:cov.monodromy (sP cov hd e q y₀ c) ⟨e.val,rfl⟩ = mark cov y₀ j c.2:=
   cov.monodromy_eq_of_map_eq s rfl
  have he:sP cov hd e q y₀ c = g.unop.trans t:=
   (endpoint cov e.val _).injective (ha.trans h.symm)
  apply MulOpposite.unop_injective
  exact (I8 _ _ (CoverKernel.inclusion (base hd).outer)).trans
   ((congrArg (fun a=>a.trans t.symm) he).trans (congrArg MulOpposite.unop ((shift t).left_inv g)))
 ·simp only [rT,LinearEquiv.trans_apply,Finsupp.domLCongr_single]
  rw [Z1]
  congr 2
  apply Subtype.ext
  rw [Q8,Rb]
  exact QZ _ _ _
end EilenbergGanea.CWPresentation
namespace EilenbergGanea.CWPresentation
open Set Topology CWCover CWCollar PathTransport CubicalSingular
open scoped ContinuousMap
universe u v
variable {X E:Type u} [TopologicalSpace X] [TopologicalSpace E]
variable [T2Space X] [CWComplex (univ:Set X)] {p:E -> X}
variable (cov:IsCoveringMap p) (hd:∀ k,2 < k -> IsEmpty (Cell (X:=X) k))
variable [PathConnectedSpace X] [ContractibleSpace E] (hs:Function.Surjective p)
include cov hd hs
theorem ordinary_boundary_basis {G:Type v} [Group G] (x:X) (χ₀:FundamentalGroup X x ≃* G) :
  ∃ (A:Type u) (a:A -> G),Function.Surjective (aD a) /\
   ∃ (r:Cell (X:=X) 2 -> FreeGroup A),(∀ j,aD a (r j)=1) /\
    (aD a).ker=Subgroup.normalClosure (Set.range r) /\
    ∃ B:aE G (Cell (X:=X) 2) ≃ₗ[ℤ] cycles a,
     ∀ c,(B c:aE G A)=aO a r c:=by
 let e:(g0 cov hd).outer:=Classical.choice inferInstance
 let q:∀ y:(g0 cov hd).outer,Path e y:=fun y=>(PathConnectedSpace.joined _ y).somePath
 let y₀:c7 2:=Classical.choice inferInstance
 let H:=FundamentalGroup (base hd).outer (root cov hd e)
 let:IsFreeGroup H:=Fe hd (root cov hd e)
 let:IsFreeGroup Hᵐᵒᵖ:=IsFreeGroup.ofMulEquiv (MulEquiv.inv' H)
 have hf:Function.Surjective (kS cov hd e):=by
  intro g
  let w:=endpoint cov e.val _ g.unop
  have hw:p w.val=p e.val:=w.property
  let z:(g0 cov hd).outer:=(y1 cov hd).symm ⟨w.val,show p w.val ∈ (base hd).outer from (congrArg (fun x=>x ∈ (base hd).outer) hw).mpr (root cov hd e).property⟩
  let s:=q z
  let t:Path (root cov hd e) (root cov hd e):=(s.map (kR cov hd).continuous).cast rfl (Subtype.ext w.property.symm)
  refine ⟨MulOpposite.op (bR t),MulOpposite.unop_injective ((endpoint cov e.val _).injective ?_)⟩
  exact cov.monodromy_eq_of_map_eq (γ:=bR (t.map continuous_subtype_val)) (ey:=w) (ex:=⟨e.val,rfl⟩) (bR (s.map continuous_subtype_val)) rfl
 let χ:(FundamentalGroup X (p e.val))ᵐᵒᵖ ≃* G:=
  (MulEquiv.inv' (FundamentalGroup X (p e.val))).symm.trans
   ((FundamentalGroup.fundamentalGroupMulEquivOfPathConnected (p e.val) x).trans χ₀)
 exact ax4.ZW
  (kS cov hd e) hf (relator cov hd e q y₀ hs)
  (Nb cov hd e q y₀ hs) (bz0 cov hd e q y₀ hs)
  (rT cov hd e q y₀ hs) (bx3 cov hd e q y₀ hs) χ
end EilenbergGanea.CWPresentation
end
end OAI
end
open OAI.EilenbergGanea in
theorem conditional_disproof (K : OAI.SimplicialChains.Contraction SeedChainCertificate.graph) : cohomologicalDimension SourceGroup = 2 ∧ ¬ HasClassifyingSpace.{0} SourceGroup 2 := by
  refine ⟨source_cd_eq_two_of_contraction K, ?_⟩
  rintro ⟨X,tX,hTX,cX,hd,hpc,x,⟨χ⟩,E,tE,hcon,p,cov,hs⟩
  let : TopologicalSpace X := tX
  let : T2Space X := hTX
  let : Topology.CWComplex (Set.univ : Set X) := cX
  let : PathConnectedSpace X := hpc
  let : TopologicalSpace E := tE
  let : ContractibleSpace E := hcon
  obtain ⟨A,a,ha,r,hr,hp,B,hB⟩ := CWPresentation.ordinary_boundary_basis cov hd hs x χ
  exact source_no_boundary_basis_of_contraction K a ha r hr hp B hB


/- Adapted from openai/math, AlgebraicTopology/{Integral/Contraction,Simplicial/Chains}. -/
namespace OAI
noncomputable section
open Classical Set
namespace FiniteIntegralContraction
section
variable {I J : Type*}
theorem map_eq_of_single [DecidableEq I] [Fintype I] {f g : (I → ℤ) →ₗ[ℤ] (J → ℤ)}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply (Pi.basisFun ℤ I).ext
  intro i
  simpa using h i

end
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K] [DecidableEq I]
def sumCoordinates : (I → ℤ) →ₗ[ℤ] ℤ where
  toFun := fun v => ∑ i, v i
  map_add' := by intros; simp [Finset.sum_add_distrib]
  map_smul' := by intros; simp [Finset.mul_sum]

@[simp] theorem sumCoordinates_single (i : I) : sumCoordinates (Pi.single i 1) = 1 := by
  simp [sumCoordinates,Pi.single_apply]

def rootCoordinates (root : I) : ℤ →ₗ[ℤ] (I → ℤ) :=
  (LinearMap.id : ℤ →ₗ[ℤ] ℤ).smulRight (Pi.single root 1)

omit [Fintype I] in
@[simp] theorem rootCoordinates_one (root : I) : rootCoordinates root 1 = Pi.single root 1 := by
  simp [rootCoordinates]

def corrected (d₁ : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (h₀ : (I → ℤ) →ₗ[ℤ] (J → ℤ))
    (h₁ : (J → ℤ) →ₗ[ℤ] (K → ℤ)) := h₁.comp (LinearMap.id - h₀.comp d₁)

/-- A stable rank equality turns a checked split boundary and a checked bottom
contraction into the full middle identity. This avoids a large redundant finite
matrix certificate; no rational exactness is substituted for integer exactness. -/
theorem middle_of_rank
    (card : Fintype.card J + 1 = Fintype.card K + Fintype.card I)
    (root : I) (d₁ : (J → ℤ) →ₗ[ℤ] (I → ℤ)) (d₂ : (K → ℤ) →ₗ[ℤ] (J → ℤ))
    (h₀ : (I → ℤ) →ₗ[ℤ] (J → ℤ)) (h₁ : (J → ℤ) →ₗ[ℤ] (K → ℤ))
    (hd : ∀ t, d₁ (d₂ (Pi.single t 1)) = 0)
    (hb : ∀ i, d₁ (h₀ (Pi.single i 1)) = Pi.single i 1 - Pi.single root 1)
    (hl : ∀ t, h₁ (d₂ (Pi.single t 1)) = Pi.single t 1) :
    (∀ t, corrected d₁ h₀ h₁ (d₂ (Pi.single t 1)) = Pi.single t 1) ∧
    (∀ j, d₂ (corrected d₁ h₀ h₁ (Pi.single j 1)) + h₀ (d₁ (Pi.single j 1)) = Pi.single j 1) := by
  have hd' : d₁.comp d₂ = 0 := map_eq_of_single hd
  have hb' : d₁.comp h₀ = LinearMap.id - (rootCoordinates root).comp sumCoordinates := by
    apply map_eq_of_single
    intro i
    simpa only [LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,
      sumCoordinates_single,rootCoordinates_one] using hb i
  have hl' : h₁.comp d₂ = LinearMap.id := map_eq_of_single hl
  have dz (t : K → ℤ) : d₁ (d₂ t) = 0 := LinearMap.congr_fun hd' t
  have bz (i : I → ℤ) : d₁ (h₀ i) = i - rootCoordinates root (sumCoordinates i) :=
    LinearMap.congr_fun hb' i
  have lz (t : K → ℤ) : h₁ (d₂ t) = t := LinearMap.congr_fun hl' t
  let F : ((K → ℤ) × (I → ℤ)) →ₗ[ℤ] ((J → ℤ) × ℤ) :=
    (((d₂.comp (LinearMap.fst ℤ _ _)) + (h₀.comp (LinearMap.snd ℤ _ _))).prod
      (sumCoordinates.comp (LinearMap.snd ℤ _ _)))
  let D : ((J → ℤ) × ℤ) →ₗ[ℤ] (I → ℤ) :=
    d₁.comp (LinearMap.fst ℤ _ _) + (rootCoordinates root).comp (LinearMap.snd ℤ _ _)
  let H : ((J → ℤ) × ℤ) →ₗ[ℤ] ((K → ℤ) × (I → ℤ)) :=
    (h₁.comp (LinearMap.fst ℤ _ _ - h₀.comp D)).prod D
  have hDF (p : (K → ℤ) × (I → ℤ)) : D (F p) = p.2 := by
    change d₁ (d₂ p.1 + h₀ p.2) + rootCoordinates root (sumCoordinates p.2) = p.2
    rw [map_add,dz,bz,zero_add,sub_add_cancel]
  have hHF (p : (K → ℤ) × (I → ℤ)) : H (F p) = p := by
    apply Prod.ext
    · change h₁ ((d₂ p.1 + h₀ p.2) - h₀ (D (F p))) = p.1
      rw [hDF,add_sub_cancel_right,lz]
    · exact hDF p
  let ei : J ⊕ Unit ≃ K ⊕ I := Fintype.equivOfCardEq (by simpa using card)
  let e : ((J → ℤ) × ℤ) ≃ₗ[ℤ] ((K → ℤ) × (I → ℤ)) :=
    (LinearEquiv.prodCongr (LinearEquiv.refl ℤ (J → ℤ)) (LinearEquiv.funUnique Unit ℤ ℤ).symm).trans
      ((LinearEquiv.sumArrowLequivProdArrow J Unit ℤ ℤ).symm.trans
        ((LinearEquiv.piCongrLeft ℤ (fun _ : K ⊕ I => ℤ) ei).trans
          (LinearEquiv.sumArrowLequivProdArrow K I ℤ ℤ)))
  have hi : Function.Injective H := IsNoetherian.injective_of_surjective_of_injective
    e.toLinearMap H e.injective (fun p => ⟨F p,hHF p⟩)
  have hFH (p : (J → ℤ) × ℤ) : F (H p) = p := hi (hHF (H p))
  constructor
  · intro t
    simp only [corrected,LinearMap.comp_apply,LinearMap.sub_apply,LinearMap.id_apply,hd,map_zero,sub_zero,hl]
  · intro j
    have he := congrArg Prod.fst (hFH (Pi.single j 1,0))
    change d₂ (h₁ (Pi.single j 1 - h₀ (d₁ (Pi.single j 1) + rootCoordinates root 0))) +
      h₀ (d₁ (Pi.single j 1) + rootCoordinates root 0) = Pi.single j 1 at he
    simpa only [map_zero,add_zero,corrected,LinearMap.comp_apply,LinearMap.sub_apply,
      LinearMap.id_apply] using he

end FiniteIntegralContraction
namespace SimplicialChains
variable {V : Type*}
theorem map_ext_single {I M : Type*} [Fintype I] [AddCommGroup M] [Module ℤ M]
    {f g : (I → ℤ) →ₗ[ℤ] M}
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) : f = g := by
  apply (Pi.basisFun ℤ I).ext
  intro i
  simpa using h i

variable [LinearOrder V] {L : SimpleGraph V}
theorem includeVec_supported {I : Type*} [Fintype I] (f : I → List V) {k : ℕ}
    (hf : ∀ i, Valid L (f i) ∧ (f i).length = k) (c : I → ℤ) :
    yP f c ∈ chains L k := by
  have he : ∃ d : I →₀ ℤ, (Pi.basisFun ℤ I).repr.symm d = c :=
    (Pi.basisFun ℤ I).repr.symm.surjective c
  obtain ⟨d,rfl⟩ := he
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simpa using Submodule.add_mem _ hc hd
  | single i n =>
    have hh : Finsupp.single (f i) (1 : ℤ) ∈ chains L k :=
      Finsupp.single_mem_supported ℤ 1 (hf i)
    have hv : (Pi.basisFun ℤ I).repr.symm (Finsupp.single i n) = n • Pi.single i 1 := by
      simp
    rw [hv,map_smul,JM]
    exact Submodule.smul_mem _ n hh

namespace TwoDimensionalIndices
variable {E T : Type*} [Fintype V] [Fintype E] [Fintype T]
variable (D : TwoDimensionalIndices (L := L) E T)
def vList (v : V) : List V := [v]
variable (root : V) (h₀ : (V → ℤ) →ₗ[ℤ] (E → ℤ))
    (h₁ : (E → ℤ) →ₗ[ℤ] (T → ℤ))

theorem fill_include_vertex (c : V → ℤ) :
    D.fill root h₀ h₁ (yP vList c) = yP D.eList (h₀ c) := by
  have hh : (D.fill root h₀ h₁).comp (yP vList) = (yP D.eList).comp h₀ := by
    apply map_ext_single
    intro i
    simp [Ej,vList]
    congr 2
    funext v
    simp [Pi.single_apply]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
theorem fill_include_edge (c : E → ℤ) :
    D.fill root h₀ h₁ (yP D.eList c) = yP D.Nd (h₁ c) := by
  have hh : (D.fill root h₀ h₁).comp (yP D.eList) = (yP D.Nd).comp h₁ := by
    apply map_ext_single
    intro i
    simp [Ej,eList,D.edge_inverse]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
theorem fill_include_triangle (c : T → ℤ) :
    D.fill root h₀ h₁ (yP D.Nd c) = 0 := by
  have hh : (D.fill root h₀ h₁).comp (yP D.Nd) = 0 := by
    apply map_ext_single
    intro i
    simp [Ej,Nd]
  exact LinearMap.congr_fun hh c

variable (d₁ : (E → ℤ) →ₗ[ℤ] (V → ℤ)) (d₂ : (T → ℤ) →ₗ[ℤ] (E → ℤ))
    (hd₁ : ∀ e, d₁ (Pi.single e 1) = Pi.single (D.edge e).2 1 - Pi.single (D.edge e).1 1)
    (hd₂ : ∀ t, d₂ (Pi.single t 1) = Pi.single (D.face t).1 1 -
      Pi.single (D.face t).2.1 1 + Pi.single (D.face t).2.2 1)

omit [Fintype T] in
include hd₁ in
theorem boundary_include_edge (c : E → ℤ) :
    boundary (yP D.eList c) = yP vList (d₁ c) := by
  have hh : boundary.comp (yP D.eList) = (yP vList).comp d₁ := by
    apply map_ext_single
    intro e
    simp [hd₁,eList,vList]
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
include hd₂ in
theorem boundary_include_triangle (c : T → ℤ) :
    boundary (yP D.Nd c) = yP D.eList (d₂ c) := by
  have hh : boundary.comp (yP D.Nd) = (yP D.eList).comp d₂ := by
    apply map_ext_single
    intro t
    obtain ⟨h₁,h₂,h₃⟩ := D.face_edge t
    simp [hd₂,Nd,eList,h₁,h₂,h₃,map_sub]
    abel
  exact LinearMap.congr_fun hh c

omit [Fintype V] in
theorem fill_degree (k : ℕ) (c : Chains V) (hc : c ∈ chains L k) :
    D.fill root h₀ h₁ c ∈ chains L (k+1) := by
  rw [chains,Finsupp.supported_eq_span_single] at hc
  apply Submodule.span_induction (p := fun c _ => D.fill root h₀ h₁ c ∈ chains L (k+1)) _ _ _ _ hc
  · rintro _ ⟨w,⟨hw,hl⟩,rfl⟩
    simp only [Nc,one_smul]
    subst k
    rcases w with _ | ⟨a,w⟩
    · exact Finsupp.single_mem_supported ℤ 1 (by simp [Valid])
    rcases w with _ | ⟨b,w⟩
    · exact includeVec_supported D.eList (fun e => ⟨D.edge_valid e,rfl⟩) _
    rcases w with _ | ⟨d,w⟩
    · exact includeVec_supported D.Nd (fun t => ⟨D.triangle_valid t,rfl⟩) _
    · exact Submodule.zero_mem _
  · simp
  · intro c d _ _ hc hd
    simpa using Submodule.add_mem _ hc hd
  · intro n c _ hc
    simpa using Submodule.smul_mem _ n hc

variable (hbottom : ∀ v, d₁ (h₀ (Pi.single v 1)) = Pi.single v 1 - Pi.single root 1)
    (hleft : ∀ t, h₁ (d₂ (Pi.single t 1)) = Pi.single t 1)
    (hmiddle : ∀ e, d₂ (h₁ (Pi.single e 1)) + h₀ (d₁ (Pi.single e 1)) = Pi.single e 1)

include hd₁ hbottom in
 theorem vertex_identity (v : V) :
    boundary (D.fill root h₀ h₁ (Finsupp.single [v] 1)) +
      D.fill root h₀ h₁ (cP [v]) = Finsupp.single [v] 1 := by
  simp only [Nc,one_smul,Ej]
  rw [D.boundary_include_edge d₁ hd₁,hbottom]
  simp [Ej,vList]

include hd₁ hd₂ hmiddle in
 theorem edge_identity (e : E) :
    boundary (D.fill root h₀ h₁ (Finsupp.single (D.eList e) 1)) +
      D.fill root h₀ h₁ (cP (D.eList e)) = Finsupp.single (D.eList e) 1 := by
  calc
    _ = boundary (D.fill root h₀ h₁ (yP D.eList (Pi.single e 1))) +
        D.fill root h₀ h₁ (boundary (yP D.eList (Pi.single e 1))) := by simp
    _ = yP D.eList (d₂ (h₁ (Pi.single e 1))) +
        yP D.eList (h₀ (d₁ (Pi.single e 1))) := by
      rw [D.fill_include_edge,D.boundary_include_triangle d₂ hd₂,
        D.boundary_include_edge d₁ hd₁,D.fill_include_vertex]
    _ = _ := by rw [← map_add,hmiddle,JM]

omit [Fintype V] in
include hd₂ hleft in
 theorem triangle_identity (t : T) :
    boundary (D.fill root h₀ h₁ (Finsupp.single (D.Nd t) 1)) +
      D.fill root h₀ h₁ (cP (D.Nd t)) = Finsupp.single (D.Nd t) 1 := by
  calc
    _ = boundary (D.fill root h₀ h₁ (yP D.Nd (Pi.single t 1))) +
        D.fill root h₀ h₁ (boundary (yP D.Nd (Pi.single t 1))) := by simp
    _ = yP D.Nd (h₁ (d₂ (Pi.single t 1))) := by
      rw [D.fill_include_triangle,map_zero,zero_add,
        D.boundary_include_triangle d₂ hd₂,D.fill_include_edge]
    _ = _ := by rw [hleft,JM]

/-- All finite matrix certificate equations are used to obtain a genuine
augmented contraction of every actual clique of the graph. -/
def contraction : Contraction L where
  homotopy := D.fill root h₀ h₁
  degree := D.fill_degree root h₀ h₁
  identity := by
    intro w hw
    have hl := D.length_le w hw
    rcases w with _ | ⟨a,w⟩
    · simp [Ej]
    rcases w with _ | ⟨b,w⟩
    · exact D.vertex_identity root h₀ h₁ d₁ hd₁ hbottom a
    rcases w with _ | ⟨c,w⟩
    · have he : D.eList (D.edgeIndex a b) = [a,b] := by
        simp [eList,D.edge_complete a b hw]
      rw [← he]
      exact D.edge_identity root h₀ h₁ d₁ d₂ hd₁ hd₂ hmiddle _
    have hw' : w = [] := by
      have hh : w.length = 0 := by simp only [List.length_cons] at hl; omega
      exact List.length_eq_zero_iff.mp hh
    subst w
    have he : D.Nd (D.triangleIndex a b c) = [a,b,c] := by
      simp [Nd,D.triangle_complete a b c hw]
    rw [← he]
    exact D.triangle_identity root h₀ h₁ d₂ hd₂ hleft _

include hd₁ hd₂ hbottom hleft in
noncomputable def contraction_of_rank (card : Fintype.card E + 1 = Fintype.card T + Fintype.card V) : Contraction L := by
  have hd (t : T) : d₁ (d₂ (Pi.single t 1)) = 0 := by
    rw [hd₂,map_add,map_sub,hd₁,hd₁,hd₁]
    obtain ⟨a,b,c⟩ := D.face_edge t
    rw [a,b,c]
    dsimp
    abel
  obtain ⟨hl,hm⟩ := FiniteIntegralContraction.middle_of_rank card root d₁ d₂ h₀ h₁ hd hbottom hleft
  exact D.contraction root h₀ _ d₁ d₂ hd₁ hd₂ hbottom hl hm
end TwoDimensionalIndices
end SimplicialChains
end
end OAI

namespace SeedReduction
-- Six barycentric flags of one oriented triangle A,B,C with side midpoints P,V,U.
-- Entries are ordered AP, BP, BV, CV, CU, AU. The common third cell is the face center.
structure Flags (M : Type*) where
  ap : M
  bp : M
  bv : M
  cv : M
  cu : M
  au : M
variable {M : Type*} [AddCommGroup M]
def total (t : Flags M) := t.ap-t.bp+t.bv-t.cv+t.cu-t.au
-- Fixed boundary half-edge values a,b at the rose and x,y on consecutive radii.
-- The center-to-radius half-edges and P-to-face edge are assigned zero.
theorem fillSector (t : Flags M) (a b x y : M) (transport : y = x+total t-(a-b)) :
    ∃ A B C U V : M,
      a-A=t.ap ∧ b-B=t.bp ∧ y+V-B=t.bv ∧ V-C=t.cv ∧ U-C=t.cu ∧ x+U-A=t.au := by
  let A := a-t.ap
  let B := b-t.bp
  let V := t.bv+B-y
  let C := V-t.cv
  let U := t.cu+C
  refine ⟨A,B,C,U,V,?_,?_,?_,?_,?_,?_⟩ <;> simp only [A,B,C,U,V,transport,total] <;> abel
-- Extend all radii around a disk, with closure imposed only on the total value.
theorem cyclicPrimitives (l : List M) (zeroPeriod : l.sum = 0) :
    ∃ r : ℕ → M, r 0 = r l.length ∧ ∀ i (hi : i < l.length), r (i+1) = r i+l[i] := by
  refine ⟨fun i => (l.take i).sum, by simp [zeroPeriod], ?_⟩
  intro i hi
  change (l.take (i+1)).sum = (l.take i).sum + l[i]
  rw [List.take_succ_eq_append_getElem hi, List.sum_append]; simp
-- The two attaching words have exponent rows (2,-5),(-1,3).
theorem solvePeriods (s t : M) : ∃ x y : M, x+x-(5:ℕ)•y=s ∧ -x+(3:ℕ)•y=t := by
  refine ⟨(3:ℕ)•s+(5:ℕ)•t,s+(2:ℕ)•t,?_,?_⟩ <;> abel

-- A cycle of sector cochains, including the wraparound radius.
theorem fillDisk {n : ℕ} (hn : 0 < n) (t : Fin n → Flags M) (a b : Fin n → M)
    (period : ∑ i, total (t i) = ∑ i, (a i-b i)) :
    ∃ r A B C U V : Fin n → M, ∀ i,
      a i-A i=(t i).ap ∧ b i-B i=(t i).bp ∧
      r ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩+V i-B i=(t i).bv ∧ V i-C i=(t i).cv ∧
      U i-C i=(t i).cu ∧ r i+U i-A i=(t i).au := by
  let delta (i : Fin n) := total (t i) - (a i-b i)
  let l := List.ofFn delta
  have hz : l.sum = 0 := by simpa [l,delta,List.sum_ofFn,Finset.sum_sub_distrib] using sub_eq_zero.mpr period
  obtain ⟨R,hwrap,hstep⟩ := cyclicPrimitives l hz
  let r (i : Fin n) := R i.val
  have hr (i : Fin n) : r ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩ = r i+total (t i)-(a i-b i) := by
    have hi : i.val < l.length := by simpa [l] using i.isLt
    have hs := hstep i.val hi
    simp only [l,List.getElem_ofFn,delta] at hs
    have hw : R 0 = R n := by simpa [l] using hwrap
    by_cases h : i.val+1 < n
    · simpa [r,Nat.mod_eq_of_lt h,sub_eq_add_neg,add_assoc] using hs
    · have he : i.val+1 = n := by omega
      simpa [r,he,hw,sub_eq_add_neg,add_assoc] using hs
  choose A B C U V h using fun i => fillSector (t i) (a i) (b i) (r i)
    (r ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩) (hr i)
  exact ⟨r,A,B,C,U,V,h⟩

inductive Letter | x | y | X | Y deriving DecidableEq, Repr
open Letter
def w0 : List Letter := [x,x,Y,Y,Y,Y,Y]
def w1 : List Letter := [x,x,y,X,y,X,y,X]
def halfBoundary (u v : M) (w : List Letter) (i : Nat) : M × M :=
  match w[i/3]?.getD x with
  | x => if i%3=0 then (u,0) else (0,0)
  | y => if i%3=0 then (v,0) else (0,0)
  | X => if i%3=2 then (0,u) else (0,0)
  | Y => if i%3=2 then (0,v) else (0,0)

def hol (u v : M) (w : List Letter) (i : Nat) : M := (halfBoundary u v w i).1-(halfBoundary u v w i).2
theorem hol0 (u v : M) : ∑ i : Fin 21, hol u v w0 i = u+u-(5:ℕ)•v := by
  simp [Fin.sum_univ_succ,hol,halfBoundary,w0]; abel
theorem hol1 (u v : M) : ∑ i : Fin 24, hol u v w1 i = -u+(3:ℕ)•v := by
  simp [Fin.sum_univ_succ,hol,halfBoundary,w1]; abel

-- Cochain integrability on the two disks sharing their subdivided rose.
def DiskSolved {n : ℕ} (hn : 0 < n) (w : List Letter) (u v : M) (t : Fin n → Flags M) : Prop :=
  ∃ r A B C U V : Fin n → M, ∀ i : Fin n,
    (halfBoundary u v w i).1-A i=(t i).ap ∧ (halfBoundary u v w i).2-B i=(t i).bp ∧
    r ⟨(i.val+1)%n,Nat.mod_lt _ hn⟩+V i-B i=(t i).bv ∧ V i-C i=(t i).cv ∧
    U i-C i=(t i).cu ∧ r i+U i-A i=(t i).au

theorem bothDisks (t0 : Fin 21 → Flags M) (t1 : Fin 24 → Flags M) :
    ∃ u v, DiskSolved (by decide) w0 u v t0 ∧ DiskSolved (by decide) w1 u v t1 := by
  obtain ⟨u,v,h₀,h₁⟩ := solvePeriods (∑ i, total (t0 i)) (∑ i, total (t1 i))
  exact ⟨u,v,fillDisk (by decide) t0 _ _ (h₀.symm.trans (hol0 u v).symm),
    fillDisk (by decide) t1 _ _ (h₁.symm.trans (hol1 u v).symm)⟩

namespace Indexed
abbrev N (b : Bool) := if b then 24 else 21
abbrev Sec := (b : Bool) × Fin (N b)
abbrev E := Fin 12 ⊕ (Sec × Fin 8)
abbrev T := Sec × Fin 6
def nxt : Sec → Sec
  | ⟨false,i⟩ => ⟨false,⟨(i.val+1)%21,Nat.mod_lt _ (by decide)⟩⟩
  | ⟨true,i⟩ => ⟨true,⟨(i.val+1)%24,Nat.mod_lt _ (by decide)⟩⟩
def letter (s : Sec) := ((if s.1 then w1 else w0)[s.2.val/3]?).getD x
def sides (z : Letter) (i : Nat) : Fin 12 × Fin 12 :=
  let pos := z==x || z==y
  let j := (if z==y || z==Y then 3 else 0)+(if pos then i%3 else 2-i%3)
  let a : Fin 12 := ⟨(2*j)%12,Nat.mod_lt _ (by decide)⟩
  let b : Fin 12 := ⟨(2*j+1)%12,Nat.mod_lt _ (by decide)⟩
  if pos then (a,b) else (b,a)
def faces : T → E × E × E
  | (s,k) =>
    let P := sides (letter s) s.2.val
    let e := fun j : Fin 8 => Sum.inr (s,j)
    match k.val with
    | 0 => (e 7,e 2,Sum.inl P.1)
    | 1 => (e 7,e 3,Sum.inl P.2)
    | 2 => (e 6,e 3,Sum.inr (nxt s,0))
    | 3 => (e 6,e 4,Sum.inr (nxt s,1))
    | 4 => (e 5,e 4,e 1)
    | _ => (e 5,e 2,e 0)
def outside (u v : M) (j : Fin 12) : M := if j.val=0 then u else if j.val=6 then v else 0
theorem halfSides (u v : M) (w : List Letter) (i : Nat) :
    (outside u v (sides (w[i/3]?.getD x) i).1,outside u v (sides (w[i/3]?.getD x) i).2) = halfBoundary u v w i := by
  generalize h : w[i/3]?.getD x = z
  unfold halfBoundary
  rw [h]
  have : i%3=0 ∨ i%3=1 ∨ i%3=2 := by omega
  rcases this with h'|h'|h' <;> cases z <;> simp [sides,outside,h']

def flag (t : T → M) (s : Sec) : Flags M := ⟨t (s,0),t (s,1),t (s,2),t (s,3),t (s,4),t (s,5)⟩

theorem integrate (t : T → M) : ∃ f : E → M, ∀ k, f (faces k).1 - f (faces k).2.1 + f (faces k).2.2 = t k := by
  obtain ⟨u,v,⟨r,A,B,C,U,V,h⟩,⟨r',A',B',C',U',V',h'⟩⟩ := bothDisks (fun i => flag t ⟨false,i⟩) (fun i => flag t ⟨true,i⟩)
  let inside (a b c d e f : M) (j : Fin 8) : M := match j.val with
    | 0 => a | 1 => 0 | 2 => b | 3 => c | 4 => d | 5 => e | 6 => f | _ => 0
  let F : E → M
    | .inl j => outside u v j
    | .inr (⟨false,i⟩,j) => inside (r i) (A i) (B i) (C i) (U i) (V i) j
    | .inr (⟨true,i⟩,j) => inside (r' i) (A' i) (B' i) (C' i) (U' i) (V' i) j
  refine ⟨F,?_⟩
  rintro ⟨⟨b,i⟩,k⟩
  cases b
  case false =>
    have hs := halfSides u v w0 i
    obtain ⟨h0,h1,h2,h3,h4,h5⟩ := h i
    dsimp only [flag] at h0 h1 h2 h3 h4 h5
    fin_cases k
    · change 0-A i+outside u v (sides (w0[i.val/3]?.getD x) i.val).1 = t (⟨false,i⟩,0)
      have he : outside u v (sides (w0[i.val/3]?.getD x) i.val).1 = (halfBoundary u v w0 i).1 := congrArg Prod.fst hs
      rw [he, ← h0]; abel
    · change 0-B i+outside u v (sides (w0[i.val/3]?.getD x) i.val).2 = t (⟨false,i⟩,1)
      have he : outside u v (sides (w0[i.val/3]?.getD x) i.val).2 = (halfBoundary u v w0 i).2 := congrArg Prod.snd hs
      rw [he, ← h1]; abel
    · change V i-B i+r ⟨(i.val+1)%21,Nat.mod_lt _ (by decide)⟩ = t (⟨false,i⟩,2)
      rw [← h2]; abel
    · change V i-C i+0 = t (⟨false,i⟩,3)
      rw [← h3]; abel
    · change U i-C i+0 = t (⟨false,i⟩,4)
      rw [← h4]; abel
    · change U i-A i+r i = t (⟨false,i⟩,5)
      rw [← h5]; abel
  case true =>
    have hs := halfSides u v w1 i
    obtain ⟨h0,h1,h2,h3,h4,h5⟩ := h' i
    dsimp only [flag] at h0 h1 h2 h3 h4 h5
    fin_cases k
    · change 0-A' i+outside u v (sides (w1[i.val/3]?.getD x) i.val).1 = t (⟨true,i⟩,0)
      have he : outside u v (sides (w1[i.val/3]?.getD x) i.val).1 = (halfBoundary u v w1 i).1 := congrArg Prod.fst hs
      rw [he, ← h0]; abel
    · change 0-B' i+outside u v (sides (w1[i.val/3]?.getD x) i.val).2 = t (⟨true,i⟩,1)
      have he : outside u v (sides (w1[i.val/3]?.getD x) i.val).2 = (halfBoundary u v w1 i).2 := congrArg Prod.snd hs
      rw [he, ← h1]; abel
    · change V' i-B' i+r' ⟨(i.val+1)%24,Nat.mod_lt _ (by decide)⟩ = t (⟨true,i⟩,2)
      rw [← h2]; abel
    · change V' i-C' i+0 = t (⟨true,i⟩,3)
      rw [← h3]; abel
    · change U' i-C' i+0 = t (⟨true,i⟩,4)
      rw [← h4]; abel
    · change U' i-A' i+r' i = t (⟨true,i⟩,5)
      rw [← h5]; abel
end Indexed
end SeedReduction
namespace SeedReduction.Indexed
open Letter
abbrev V := Fin 103
def vertex (n : Nat) : V := ⟨n%103,Nat.mod_lt _ (by decide)⟩
def secNo (s : Sec) := (if s.1 then 21 else 0)+s.2.val
def unpack (n : Nat) : Sec := if n<21 then ⟨false,⟨n%21,Nat.mod_lt _ (by decide)⟩⟩ else ⟨true,⟨(n-21)%24,Nat.mod_lt _ (by decide)⟩⟩
def rosePt (j : Nat) : V := let i := (j/2%3+j%2)%3; vertex (if i=0 then 0 else 2*(j/6)+i)
def endpoints : E → V × V
 | .inl j => (rosePt j.val,vertex (7+j.val/2))
 | .inr (s,k) =>
   let n := secNo s
   let p := sides (letter s) s.2.val
   let a := rosePt p.1.val
   let b := rosePt p.2.val
   let o := vertex (if s.1 then 6 else 5)
   let r := vertex (13+n)
   let t := vertex (58+n)
   match k.val with
   | 0 => (a,r) | 1 => (o,r) | 2 => (a,t) | 3 => (b,t) | 4 => (o,t)
   | 5 => (r,t) | 6 => (vertex (13+secNo (nxt s)),t) | _ => (vertex (7+p.1.val/2),t)
def vertices (t : T) : V × V × V := let f := faces t; ((endpoints f.2.2).1,(endpoints f.1).1,(endpoints f.1).2)
def decodeE (a b : V) : E :=
 if b.val < 13 then let j := 2*(b.val-7); .inl (Fin.ofNat 12 (if rosePt j=a then j else j+1))
 else if b.val < 58 then .inr (unpack (b.val-13),if a.val<5 then 0 else 1)
 else let s := unpack (b.val-58); let p := sides (letter s) s.2.val
      .inr (s,if a.val<5 then (if a=rosePt p.1.val then 2 else 3) else if a.val<7 then 4 else if a.val<13 then 7 else if a.val=13+secNo s then 5 else 6)
def decodeT (a b c : V) : T := let s := unpack (c.val-58); let p := sides (letter s) s.2.val
 (s,if b.val<13 then (if a=rosePt p.1.val then 0 else 1) else if b.val=13+secNo s then (if a.val<5 then 5 else 4) else (if a.val<5 then 2 else 3))
end SeedReduction.Indexed
namespace SeedReduction.Indexed
open OAI.EilenbergGanea.SeedEncoding
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
abbrev ok (a b : V) := a < b ∧ indexedAdj a b
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
abbrev ev (e : E) := ok (endpoints e).1 (endpoints e).2 ∧ decodeE (endpoints e).1 (endpoints e).2 = e
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkE : ∀ e, ev e := by
  rintro (j|⟨⟨b,i⟩,k⟩)
  · revert j; decide +kernel
  · cases b <;> revert i k <;> decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem coverE : ∀ a b, ok a b → endpoints (decodeE a b) = (a,b) := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
abbrev tv (t : T) := let (a,b,c) := vertices t; let (x,y,z) := faces t
  ok a b ∧ ok b c ∧ ok a c ∧ endpoints x = (b,c) ∧ endpoints y = (a,c) ∧ endpoints z = (a,b)
set_option maxRecDepth 100000 in
set_option maxHeartbeats 8000000 in
theorem checkT : ∀ t, tv t := by
  rintro ⟨⟨b,i⟩,k⟩; cases b <;> revert i k <;> decide +kernel
end SeedReduction.Indexed
namespace SeedReduction.Indexed
open OAI.SimplicialChains OAI.EilenbergGanea OAI.EilenbergGanea.SeedChainCertificate
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
abbrev etc (e : E) (c : V) := let (a,b) := endpoints e; ok a c → ok b c → vertices (decodeT a b c) = (a,b,c)
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem coverFinal : ∀ e c, etc e c := by
  rintro (j|⟨⟨b,i⟩,k⟩)
  · revert j; decide +kernel
  · cases b <;> revert i k <;> decide +kernel
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem pair (a b : V) : Valid graph [a,b] ↔ ok a b := by simp [Valid,ok,graph_adj]
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
theorem triple (a b c : V) : Valid graph [a,b,c] ↔ ok a b ∧ ok a c ∧ ok b c := by
  simp [Valid,ok,graph_adj]; tauto
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 100000 in
def idx : TwoDimensionalIndices (L:=graph) E T where
  edge := endpoints
  triangle := vertices
  face := faces
  edgeIndex := decodeE
  triangleIndex := decodeT
  edge_valid e := (pair _ _).2 (checkE e).1
  triangle_valid t := (triple _ _ _).2 ⟨(checkT t).1,(checkT t).2.2.1,(checkT t).2.1⟩
  edge_inverse e := (checkE e).2
  edge_complete a b h := coverE _ _ ((pair _ _).1 h)
  triangle_complete a b c h := by
    obtain ⟨ab,ac,bc⟩ := (triple _ _ _).1 h
    have H := coverFinal (decodeE a b) c
    unfold etc at H
    rw [coverE a b ab] at H
    exact H ac bc
  face_edge t := (checkT t).2.2.2
  length_le := valid_length_le
end SeedReduction.Indexed

namespace SeedReduction
open Classical
noncomputable section
variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
variable (G : SimpleGraph V) (edge : E → V × V)
  (d : (E → ℤ) →ₗ[ℤ] (V → ℤ))
  (boundary : ∀ e, d (Pi.single e 1) = Pi.single (edge e).2 1 - Pi.single (edge e).1 1)
  (spans : ∀ v w, G.Adj v w → ∃ e, edge e = (v,w) ∨ edge e = (w,v))
include boundary spans in
theorem pathBoundary {v w : V} (p : G.Walk v w) :
    ∃ c, d c = Pi.single w 1 - Pi.single v 1 := by
  induction p with
  | nil => exact ⟨0, by simp⟩
  | @cons a b c h p ih =>
    obtain ⟨e,h'|h'⟩ := spans a b h
    · obtain ⟨x,hx⟩ := ih
      exact ⟨x + Pi.single e 1, by rw [map_add,hx,boundary,h']; dsimp; abel⟩
    · obtain ⟨x,hx⟩ := ih
      exact ⟨x - Pi.single e 1, by rw [map_sub,hx,boundary,h']; dsimp; abel⟩
include boundary spans in
theorem bottomSplit (root : V) (conn : G.Preconnected) :
    ∃ f : (V → ℤ) →ₗ[ℤ] (E → ℤ), ∀ v, d (f (Pi.single v 1)) = Pi.single v 1 - Pi.single root 1 := by
  choose col hc using fun v => pathBoundary G edge d boundary spans (conn root v).some
  let f := (Pi.basisFun ℤ V).constr ℤ col
  refine ⟨f, fun v => ?_⟩
  have h : f ((Pi.basisFun ℤ V) v) = col v := (Pi.basisFun ℤ V).constr_basis ℤ col v
  rw [← hc v, ← h]; simp
end
end SeedReduction

namespace SeedReduction.Indexed
noncomputable section
open OAI.EilenbergGanea OAI.EilenbergGanea.SeedChainCertificate
open Classical
abbrev Z (A : Type) := A → ℤ
def lin {A B : Type} [Fintype A] (f : A → Z B) := (Pi.basisFun ℤ A).constr ℤ f
theorem lin_one {A B : Type} [Fintype A] [DecidableEq A] (f : A → Z B) (a : A) : lin f (Pi.single a 1) = f a := by
  simpa only [lin, Pi.basisFun_apply] using (Pi.basisFun ℤ A).constr_basis ℤ f a
def bd1 (e : E) : Z V := Pi.single (endpoints e).2 1 - Pi.single (endpoints e).1 1
def bd2 (t : T) : Z E := Pi.single (faces t).1 1 - Pi.single (faces t).2.1 1 + Pi.single (faces t).2.2 1
theorem zero_comp (t : T) : lin bd1 (lin bd2 (Pi.single t 1)) = 0 := by
  rw [lin_one, bd2, map_add, map_sub,lin_one,lin_one,lin_one]
  obtain ⟨h,k,l⟩ := idx.face_edge t
  change endpoints (faces t).1 = _ at h
  change endpoints (faces t).2.1 = _ at k
  change endpoints (faces t).2.2 = _ at l
  simp only [bd1,h,k,l]; abel
theorem split_left : ∃ h : Z E →ₗ[ℤ] Z T, ∀ t, h (lin bd2 (Pi.single t 1)) = Pi.single t 1 := by
  obtain ⟨f,hf⟩ := integrate (fun t : T => Pi.single t (1:ℤ))
  exact ⟨lin f,fun t => by rw [lin_one,bd2,map_add,map_sub,lin_one,lin_one,lin_one]; exact hf t⟩
theorem split_bottom : ∃ h : Z V →ₗ[ℤ] Z E, ∀ v, lin bd1 (h (Pi.single v 1)) = Pi.single v 1 - Pi.single (0:V) 1 := by
  apply SeedReduction.bottomSplit graph endpoints (lin bd1) (fun e => lin_one bd1 e) _ 0
  · exact (SimpleGraph.Iso.comap SeedEncoding.cellEquiv.symm seedGraph).preconnected_iff.mpr seed_connected.preconnected
  · intro a b h
    rcases lt_trichotomy a b with hab|rfl|hba
    · exact ⟨decodeE a b,Or.inl (coverE a b ⟨hab,(graph_adj a b).1 h⟩)⟩
    · exact False.elim (h.ne rfl)
    · exact ⟨decodeE b a,Or.inr (coverE b a ⟨hba,(graph_adj b a).1 h.symm⟩)⟩
theorem size_id : Fintype.card E + 1 = Fintype.card T + Fintype.card V := by
  simp [E,T,Sec,N,Fintype.card_sigma,Fintype.sum_bool]
end
end SeedReduction.Indexed

namespace SeedReduction.Indexed
open OAI.EilenbergGanea
set_option maxRecDepth 20000 in
set_option maxHeartbeats 3000000 in
noncomputable def seedContraction : OAI.SimplicialChains.Contraction SeedChainCertificate.graph := by
  have he : (fun (a b : E) => Classical.propDecidable (a=b)) = (inferInstance : DecidableEq E) := Subsingleton.elim _ _
  have ht : (fun (a b : T) => Classical.propDecidable (a=b)) = (inferInstance : DecidableEq T) := Subsingleton.elim _ _
  apply idx.contraction_of_rank 0 split_bottom.choose split_left.choose (lin bd1) (lin bd2)
    
  · rw [he]; exact lin_one bd1
  · rw [ht, he]; exact lin_one bd2
  · exact split_bottom.choose_spec
  · rw [ht]; exact split_left.choose_spec
  · exact size_id
end SeedReduction.Indexed
namespace OAI.EilenbergGanea
theorem source_cohomologicalDimension : cohomologicalDimension SourceGroup = 2 :=
  (conditional_disproof SeedReduction.Indexed.seedContraction).1
theorem source_no_classifyingSpace_two : ¬ HasClassifyingSpace.{0} SourceGroup 2 :=
  (conditional_disproof SeedReduction.Indexed.seedContraction).2
end OAI.EilenbergGanea

open OAI.EilenbergGanea in
theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_eilenberg_ganea_conjecture.main) := by
  intro h
  exact source_no_classifyingSpace_two (h SourceGroup source_cohomologicalDimension)
