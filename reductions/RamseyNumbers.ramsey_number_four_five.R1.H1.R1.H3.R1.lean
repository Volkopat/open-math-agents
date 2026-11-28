import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1
import Mathlib

/-!
Each of the 179 triangle-free eight-vertex graphs with independence number
at most four contains one of the 25 induced graphs in H1. It suffices to
rule out crossings to the fixed right block for those five six-vertex,
sixteen seven-vertex and four eight-vertex graphs. A monochromatic clique
consists of subsets of the same colour on the two sides, with every
crossing edge between them of that colour.
-/

open Finset SimpleGraph
namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1

def H1 : Prop :=
  ∀ L : SimpleGraph (Fin 8), L.CliqueFree 3 → Lᶜ.CliqueFree 5 →
    ∃ p ∈ ([(6,2112),(6,3136),(6,4232),(6,6208),(6,14400),(7,236608),(7,332992),(7,368064),(7,396480),(7,433344),(7,437696),(7,439488),(7,466056),(7,472256),(7,494784),(7,496832),(7,498752),(7,506944),(7,507840),(7,922816),(7,924864),(8,31956160),(8,31960512),(8,59186376),(8,59227328)] : List (ℕ × ℕ)), ∃ e : Fin p.1 ↪ Fin 8, ∀ i j, i<j →
      (L.Adj (e i) (e j) ↔ p.2.testBit (j.val*(j.val-1)/2+i.val) = true)

def H2 : Prop :=
  ∀ p ∈ ([(6,2112),(6,3136),(6,4232),(6,6208),(6,14400)] : List (ℕ × ℕ)), ∀ rows : Fin p.1 → Fin 16 → Bool,
    ∃ (c : Bool) (s : Finset (Fin p.1)) (t : Finset (Fin 16)),
    s.card + t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i < j → p.2.testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i < j →
      (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j = c

def H3 : Prop :=
  ∀ p ∈ ([(7,236608),(7,332992),(7,368064),(7,396480),(7,433344),(7,437696),(7,439488),(7,466056),(7,472256),(7,494784),(7,496832),(7,498752),(7,506944),(7,507840),(7,922816),(7,924864)] : List (ℕ × ℕ)), ∀ rows : Fin p.1 → Fin 16 → Bool,
    ∃ (c : Bool) (s : Finset (Fin p.1)) (t : Finset (Fin 16)),
    s.card + t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i < j → p.2.testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i < j →
      (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j = c

def H4 : Prop :=
  ∀ p ∈ ([(8,31956160),(8,31960512),(8,59186376),(8,59227328)] : List (ℕ × ℕ)), ∀ rows : Fin p.1 → Fin 16 → Bool,
    ∃ (c : Bool) (s : Finset (Fin p.1)) (t : Finset (Fin 16)),
    s.card + t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i < j → p.2.testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i < j →
      (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j = c

theorem lift_colour {V : Type*} {G : SimpleGraph V} {x y : V} {v c : Bool}
    (hne : x ≠ y) (hx : G.Adj x y ↔ v = true) (hc : v = c) :
    (if c then G else Gᶜ).Adj x y := by
  subst v
  cases c
  · exact ⟨hne,fun h => Bool.false_ne_true (hx.mp h)⟩
  · exact hx.mpr rfl

/-- The two ordered blocks give an actual clique of the sum of their sizes. -/
theorem glue_clique {G : SimpleGraph (Fin 24)} {n : ℕ} (e : Fin n ↪ Fin 8)
    (s : Finset (Fin n)) (t : Finset (Fin 16))
    (hl : ∀ i ∈ s, ∀ j ∈ s, i<j → G.Adj (Fin.castAdd 16 (e i)) (Fin.castAdd 16 (e j)))
    (hr : ∀ i ∈ t, ∀ j ∈ t, i<j → G.Adj (Fin.natAdd 8 i) (Fin.natAdd 8 j))
    (hm : ∀ i ∈ s, ∀ j ∈ t, G.Adj (Fin.castAdd 16 (e i)) (Fin.natAdd 8 j)) :
    ¬G.CliqueFree (s.card+t.card) := by
  classical
  let l (i : Fin n) : Fin 24 := Fin.castAdd 16 (e i)
  let r (j : Fin 16) : Fin 24 := Fin.natAdd 8 j
  have li : Function.Injective l := by
    intro i j h
    apply e.injective
    exact Fin.ext (congrArg (fun x : Fin 24 => x.val) h)
  have ri : Function.Injective r := by
    intro i j h
    have eq := congrArg (fun x : Fin 24 => x.val) h
    change 8+i.val=8+j.val at eq
    exact Fin.ext (by omega)
  have sep (i : Fin n) (j : Fin 16) : l i ≠ r j := by
    intro h
    have eq := congrArg (fun x : Fin 24 => x.val) h
    change (e i).val=8+j.val at eq
    have := (e i).isLt
    omega
  have dis : Disjoint (s.image l) (t.image r) := by
    refine Finset.disjoint_left.mpr ?_
    intro x hx hy
    obtain ⟨i,_,rfl⟩ := mem_image.mp hx
    obtain ⟨j,_,hj⟩ := mem_image.mp hy
    exact sep i j hj.symm
  intro free
  apply free (s.image l ∪ t.image r)
  refine ⟨?_,by rw [Finset.card_union_of_disjoint dis,card_image_of_injective _ li,
    card_image_of_injective _ ri]⟩
  intro x hx y hy hxy
  rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    rcases lt_or_gt_of_ne (fun h : i=j => hxy (congrArg l h)) with h|h
    · exact hl i hi j hj h
    · exact (hl j hj i hi h).symm
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    exact hm i hi j hj
  · obtain ⟨j,hj,rfl⟩ := mem_image.mp hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hy
    exact (hm i hi j hj).symm
  · obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hy
    rcases lt_or_gt_of_ne (fun h : i=j => hxy (congrArg r h)) with h|h
    · exact hr i hi j hj h
    · exact (hr j hj i hi h).symm

theorem main : H1 → H2 → H3 → H4 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1.H3 := by
  classical
  intro census six seven eight G hg hc hleft right
  let emb : Fin 8 ↪ Fin 24 := ⟨Fin.castAdd 16, fun _ _ h => Fin.ext (congrArg (fun x : Fin 24 => x.val) h)⟩
  let L := G.comap emb
  let incl : L ↪g G := SimpleGraph.Embedding.comap emb G
  have lc : Lᶜ.CliqueFree 5 := hc.comap (SimpleGraph.Embedding.complEquiv incl).isContained
  obtain ⟨p,hp,e,left⟩ := census L hleft lc
  let rows (i : Fin p.1) (j : Fin 16) := decide (G.Adj (Fin.castAdd 16 (e i)) (Fin.natAdd 8 j))
  have found : ∃ (c : Bool) (s : Finset (Fin p.1)) (t : Finset (Fin 16)),
    s.card + t.card = (if c then 4 else 5) ∧
    (∀ i ∈ s, ∀ j ∈ s, i < j → p.2.testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    (∀ i ∈ t, ∀ j ∈ t, i < j →
      (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val) = c) ∧
    ∀ i ∈ s, ∀ j ∈ t, rows i j = c := by
    change p ∈ ([(6,2112),(6,3136),(6,4232),(6,6208),(6,14400)] : List (ℕ × ℕ)) ++ (([(7,236608),(7,332992),(7,368064),(7,396480),(7,433344),(7,437696),(7,439488),(7,466056),(7,472256),(7,494784),(7,496832),(7,498752),(7,506944),(7,507840),(7,922816),(7,924864)] : List (ℕ × ℕ)) ++ ([(8,31956160),(8,31960512),(8,59186376),(8,59227328)] : List (ℕ × ℕ))) at hp
    rcases List.mem_append.mp hp with h|h
    · exact six p h rows
    rcases List.mem_append.mp h with h|h
    · exact seven p h rows
    · exact eight p h rows
  obtain ⟨c,s,t,size,hs,ht,hm⟩ := found
  apply glue_clique (G:=if c then G else Gᶜ) e s t ?_ ?_ ?_
  · cases c
    · simpa [size] using hc
    · simpa [size] using hg
  · intro i hi j hj h
    apply lift_colour (G:=G) (x:=Fin.castAdd 16 (e i)) (y:=Fin.castAdd 16 (e j)) (v:=p.2.testBit (j.val*(j.val-1)/2+i.val)) ?_ (left i j h) (hs i hi j hj h)
    intro eq
    apply (ne_of_lt h)
    exact e.injective (Fin.ext (congrArg (fun x : Fin 24 => x.val) eq))
  · intro i hi j hj h
    apply lift_colour (v:=(0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val))
      ?_ (right i j h) (ht i hi j hj h)
    intro eq
    have val := congrArg (fun x : Fin 24 => x.val) eq
    change 8+i.val=8+j.val at val
    exact (ne_of_lt h) (Fin.ext (by omega))
  · intro i hi j hj
    apply lift_colour (v:=rows i j) ?_ (by simp [rows]) (hm i hi j hj)
    intro eq
    have val := congrArg (fun x : Fin 24 => x.val) eq
    change (e i).val=8+j.val at val
    have := (e i).isLt
    omega

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1
