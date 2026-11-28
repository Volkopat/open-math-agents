import OMAStatements.S_mo_178849
/- Adapted from OpenAI openai/math@3344da59991ed94f9ba711217b29c1d760badfa6. -/
open Set
open scoped Pointwise Classical
namespace OMA.R_mo_178849_R1
noncomputable section
def H1 : Prop := ∀ (V:Type) [NormedAddCommGroup V] [NormedSpace ℝ V],
 let C:=Geometry.SimplicialComplex ℝ V
 let c (s:Finset V):=convexHull ℝ (s:Set V)
 let hs (p:Set V):=∃ (l:V→ₗ[ℝ] ℝ) (r:ℝ),p={x | l x≤r}
 let act (s:Finset V) (A:Finset (Set V)):=(A.image (fun p=> c s∩p)).filter (fun q=> q.Nonempty∧q ≠ c s)
 ∃ F:Finset V→Finset (Set V)→C,∀ (K:C) (A:Finset V→Finset (Set V)),
 (∀ s∈K.faces,∀ p∈A s,hs p)→(∀ s∈K.faces,∀ t⊆s,t.Nonempty→act t (A s)=act t (A t))→
 ∃ G:C,G.faces={u | ∃ s∈K.faces,u∈(F s (A s)).faces}∧G.space=K.space∧
 ∀ s∈K.faces,let L:=F s (A s)
 L.faces.Finite∧L.space=c s∧{u∈G.faces | (u:Set V)⊆c s}=L.faces∧
 (∀ u∈G.faces,c u∩c s=convexHull ℝ ((u:Set V)∩c s))∧
 (∀ u∈L.faces,∀ (l:V→ₗ[ℝ] ℝ) (r:ℝ),{x | l x≤r}∈A s→c u⊆{x | l x≤r}∨c u⊆{x | r≤l x})∧
 ∀ e:V ≃L[ℝ] V,(F (s.map e.toEquiv.toEmbedding) ((A s).image (fun p=> e '' p))).faces=(fun u:Finset V=> u.map e.toEquiv.toEmbedding) '' L.faces
open Set MeasureTheory Finsupp Geometry TopologicalSpace
def H2 : Prop := ∀(H Y:Type)(X:Profinite.{0})[Group H][Countable H][Countable Y][LinearOrder Y][MulAction H Y][IsCancelSMul H Y][MulAction H X][ContinuousConstSMul H X][IsCancelSMul H X],letI:=borel X;∀μ:ProbabilityMeasure X,(∀h:H,MeasurePreserving (h•·:X→X) μ μ)→∀(G:SimpleGraph Y)[G.LocallyFinite],G.Connected→(∀(h:H) u v,G.Adj (h•u) (h•v)↔G.Adj u v)→∀D n:ℕ,2≤D→(∀y,G.degree y≤D)→(4*D^3+D+3)^2≤n→∀T:Finset (Finset Y),(∀t∈T,t.card=n+1∧(G.induce ↑t).Connected)→
 (∀(V:Type)[NormedAddCommGroup V][NormedSpace ℝ V],let c (s:Finset V):=convexHull ℝ ↑s;let C:=SimplicialComplex ℝ V;let w s (A:Finset _):=(A.image (c s∩·)).filter fun q↦q.Nonempty∧q≠c s;∃Φ:_→_→C,∀L:C,∀A:_→Finset (Set V),(∀s∈L.faces,∀p∈A s,∃l:V→ₗ[ℝ]ℝ,∃r,p={x|l x≤r})→(∀s∈L.faces,∀t⊆s,t.Nonempty→w t (A s)=w t (A t))→∃M:C,M.space=L.space∧∀s∈L.faces,let N:=Φ s (A s);N.faces.Finite∧N.space=c s∧{u∈M.faces|↑u⊆c s}=N.faces∧(∀u∈M.faces,c u∩c s=convexHull ℝ (↑u∩c s))∧(∀u∈N.faces,∀(l:V→ₗ[ℝ]ℝ) r,{x|l x≤r}∈A s→c u⊆{x|l x≤r}∨c u⊆{x|r≤l x})∧∀e:V≃L[ℝ]V,(Φ (s.image e) ((A s).image (e ''·))).faces=(·.image e)''N.faces)→
 let V:=Y→₀ℝ
 let S:=SimplicialComplex ℝ V
 let c (s:Finset V):=convexHull ℝ ↑s
 let a (h:H):=mapDomain (M:=ℝ) (h•·)
 ∀K:S,K.faces=(·.image (single · 1))''{s|s.Nonempty∧∃h:H,∃t∈T,s⊆h•t}→
 ∃C:Finset V→ℝ,∀ε>0,∃(Z:ℕ→X→S) (P:_→_→Set V),(∀s∈K.faces,s.card=n+1→∫x,((P 0 x∩c s).ncard:ℝ)∂μ≤C s*ε)∧(∀i x,∀v∈P i x,∃s∈(Z i x).faces,v∈c s∧c s⊆P i x)∧(∀i,∀t∈K.faces,IsLocallyConstant fun x↦({s∈(Z i x).faces|↑s⊆c t},P i x∩c t))∧(∀i h x,(·.image (a h))''(Z i x).faces⊆(Z i (h•x)).faces∧a h ''P i x⊆P i (h•x))∧(∀x,Z n x=K∧P n x=K.space)∧∀i<n,∀x,(Z i x).space=K.space∧(∀t∈(Z (i+1) x).faces,(∀s∈(Z i x).faces,c s∩c t=convexHull ℝ (↑s∩c t))∧{s∈(Z i x).faces|↑s⊆c t}.Finite)∧P i x⊆P (i+1) x∧(∀t∈(Z (i+1) x).faces,c t⊆P (i+1) x→∀s∈(Z i x).faces,c s⊆c t∩P i x→s.card<t.card)∧∀A⊆P (i+1) x\P i x,IsPreconnected ((linearCombination ℝ (lp.single 2 · (1:ℝ)))''A)→∀p∈A,∀q∈A,sSup {r|∃f:Y→ℝ,(∀u v,f u-f v≤G.dist u v)∧linearCombination ℝ f (p-q)=r}≤8*D^2*√n
def H3 : Prop := ∀(H Y:Type)[Group H][Countable H][Countable Y][LinearOrder Y][MulAction H Y][IsCancelSMul H Y](_:Y)(G:SimpleGraph Y)[G.LocallyFinite],G.Connected→(∀(h:H) u v,G.Adj (h•u) (h•v)↔G.Adj u v)→∀D n:ℕ,2≤D→(∀y,G.degree y≤D)→(4*D^3+D+3)^2≤n→∀T:Finset (Finset Y),(∀t∈T,t.card=n+1∧(G.induce ↑t).Connected)→
(∀(X:Profinite.{0})[MulAction H X][ContinuousConstSMul H X][IsCancelSMul H X],letI:=borel X;∀μ:ProbabilityMeasure X,(∀h:H,MeasurePreserving (h•·:X→X) μ μ)→
 let V:=Y→₀ℝ
 let S:=SimplicialComplex ℝ V
 let c (s:Finset V):=convexHull ℝ ↑s
 let a (h:H):=mapDomain (M:=ℝ) (h•·)
 ∀K:S,K.faces=(·.image (single · 1))''{s|s.Nonempty∧∃h:H,∃t∈T,s⊆h•t}→
 ∃C:Finset V→ℝ,∀ε>0,∃(Z:ℕ→X→S) (P:_→_→Set V),(∀s∈K.faces,s.card=n+1→∫x,((P 0 x∩c s).ncard:ℝ)∂μ≤C s*ε)∧(∀i x,∀v∈P i x,∃s∈(Z i x).faces,v∈c s∧c s⊆P i x)∧(∀i,∀t∈K.faces,IsLocallyConstant fun x↦({s∈(Z i x).faces|↑s⊆c t},P i x∩c t))∧(∀i h x,(·.image (a h))''(Z i x).faces⊆(Z i (h•x)).faces∧a h ''P i x⊆P i (h•x))∧(∀x,Z n x=K∧P n x=K.space)∧∀i<n,∀x,(Z i x).space=K.space∧(∀t∈(Z (i+1) x).faces,(∀s∈(Z i x).faces,c s∩c t=convexHull ℝ (↑s∩c t))∧{s∈(Z i x).faces|↑s⊆c t}.Finite)∧P i x⊆P (i+1) x∧(∀t∈(Z (i+1) x).faces,c t⊆P (i+1) x→∀s∈(Z i x).faces,c s⊆c t∩P i x→s.card<t.card)∧∀A⊆P (i+1) x\P i x,IsPreconnected ((linearCombination ℝ (lp.single 2 · (1:ℝ)))''A)→∀p∈A,∀q∈A,sSup {r|∃f:Y→ℝ,(∀u v,f u-f v≤G.dist u v)∧linearCombination ℝ f (p-q)=r}≤8*D^2*√n)→
 let E:=fun k↦⋀[ℂ]^k (Y→₀ℂ)
 let w:=fun k (v:Fin k→Y)↦exteriorPower.ιMulti ℂ k fun i↦single (v i) (1:ℂ)
 let S:=fun k↦Submodule.span ℂ {x|∃v:Fin k→Y,(Finset.univ.image v∈insert ∅ {s:Finset Y|s.Nonempty∧∃h:H,∃t∈T,s⊆h•t})∧w k v=x}
 let a:=fun k (h:H)↦exteriorPower.map k (lmapDomain ℂ ℂ fun y:Y↦h•y)
 ∀d:∀k,E (k+1)→ₗ[ℂ] E k,(∀k v,d k (w (k+1) v)=∑i:Fin (k+1),(-1:ℂ)^i.val•w k (v ∘ i.succAbove))→∀(c:S (n+1)) (ψ:E (n+1)→ₗ[ℂ] ℂ) (δ:ℝ),0<δ→∃A:∀k,E k→ₗ[ℂ] E k,(∀x,A 0 x=x)∧(∀k x,x∈S (k+1)→d k (A (k+1) x)=A k (d k x))∧(∀k h x,x∈S k→a k h (A k x)=A k (a k h x))∧‖ψ (A (n+1) c)‖<δ
def H4 : Prop := (∀ (H Y:Type) [Group H] [Countable H] [Countable Y] [LinearOrder Y]
 [MulAction H Y] [IsCancelSMul H Y] (_:Y) (G:SimpleGraph Y) [G.LocallyFinite],
 G.Connected→(∀ (h:H) u v,G.Adj (h•u) (h•v)↔G.Adj u v)→
 ∀ (D n:ℕ),2≤D→(∀ y,Fintype.card (G.neighborSet y)≤D)→
 (4*D^3+D+3)^2≤n→∀ T:Finset (Finset Y),
 (∀ t∈T,t.card=n+1∧(G.induce (t:Set Y)).Connected)→
 let E:=fun k=> ⋀[ℂ]^k (Y→₀ ℂ)
 let w:=fun k (v:Fin k→Y)=> exteriorPower.ιMulti ℂ k (fun i=> Finsupp.single (v i) (1:ℂ))
 let S:=fun k=> Submodule.span ℂ {x | ∃ v:Fin k→Y,
 (Finset.univ.image v∈insert ∅ {s:Finset Y | s.Nonempty∧∃ h:H,∃ t∈T,s⊆h•t})∧w k v=x}
 let a:=fun k (h:H)=> exteriorPower.map k (Finsupp.lmapDomain ℂ ℂ (fun y:Y=> h•y))
 ∀ (d:∀ k,E (k+1)→ₗ[ℂ] E k),
 (∀ k v,d k (w (k+1) v)=∑ i:Fin (k+1),(-1:ℂ)^i.val•w k (v ∘ i.succAbove))→
 ∀ (c:S (n+1)) (ψ:E (n+1)→ₗ[ℂ] ℂ) (δ:ℝ),0<δ→
 ∃ A:∀ k,E k→ₗ[ℂ] E k,(∀ x,A 0 x=x)∧
 (∀ k x,x∈S (k+1)→d k (A (k+1) x)=A k (d k x))∧
 (∀ k h x,x∈S k→a k h (A k x)=A k (a k h x))∧‖ψ (A (n+1) c)‖<δ) → ∀ (G : Type) [Group G], OMA.S_mo_178849.TorsionFree G → OMA.S_mo_178849.HasOnlyTrivialIdempotents G
open OMA.S_mo_178849
theorem torsionFree_middle {N G Q : Type*} [Group N] [Group G] [Group Q]
    (i : N →* G) (p : G →* Q) (hi : Function.Injective i)
    (hex : i.range = p.ker)
    (hN : ∀ n : N, IsOfFinOrder n → n = 1)
    (hQ : ∀ q : Q, IsOfFinOrder q → q = 1) :
    ∀ g : G, IsOfFinOrder g → g = 1 := by
  intro g hg
  have hpg : p g = 1 := by
    obtain ⟨n, hn, he⟩ := hg.exists_pow_eq_one
    exact hQ _ (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by rw [← map_pow, he, map_one]⟩)
  have hr : g ∈ i.range := hex.symm ▸ (show g ∈ p.ker from hpg)
  obtain ⟨n, rfl⟩ := hr
  rw [hN n (hi.isOfFinOrder_iff.mp hg), map_one]



theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_mo_178849.main := by
  intro g a b ha
  have scalar := ha (by
    classical
    intro H Y _ _ _ _ _ _ y G _ hG ha D n hD hd hn T ht
    have hd' : ∀y,G.degree y≤D := fun y => by simpa only [SimpleGraph.card_neighborSet_eq_degree] using hd y
    apply b H Y y G hG ha D n hD hd' hn T ht
    intro X _ _ _ μ hμ
    refine a H Y X μ hμ G hG ha D n hD hd' hn T ht ?_
    intro V _ _ c C w
    obtain ⟨F,hF⟩ := g V
    refine ⟨F,?_⟩
    intro L A hA hres
    obtain ⟨M,_,he,h⟩ := hF L A hA hres
    refine ⟨M,he,?_⟩
    intro t ht
    obtain ⟨hf,hs,htr,hi,hc,hnat⟩ := h t ht
    refine ⟨hf,hs,htr,hi,hc,?_⟩
    intro e
    have he (t : Finset V) : t.map e.toEquiv.toEmbedding = t.image e := by
      ext u
      simp only [Finset.mem_map,Finset.mem_image]
      rfl
    simpa only [he] using hnat e)
  let ses : ∀ (N G Q : Type) [Group N] [Group G] [Group Q] (i : N →* G) (p : G →* Q), Function.Injective i → i.range = p.ker → TorsionFree N → TorsionFree Q → HasOnlyTrivialIdempotents G := by
    intro N G Q _ _ _ i p hi hex hn hq e he
    exact scalar _ (torsionFree_middle i p hi hex hn hq) e he
  constructor
  · intro N G Q _ _ _ i p hi _ hex hn hq _ _
    exact ses N G Q i p hi hex hn hq
  · intro N H _ _ φ hn hh _ _
    exact ses N (N ⋊[φ] H) H SemidirectProduct.inl SemidirectProduct.rightHom SemidirectProduct.inl_injective SemidirectProduct.range_inl_eq_ker_rightHom hn hh

end
end OMA.R_mo_178849_R1
