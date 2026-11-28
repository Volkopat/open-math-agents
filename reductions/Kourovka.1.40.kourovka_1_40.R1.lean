import FormalConjectures.Kourovka.«1_40»
import Mathlib

-- Reduction Kourovka.1.40.kourovka_1_40.R1 of Kourovka problem 1.40 (Kemkhadze): if a group is the
-- product of two normal Engel subgroups (nilsubgroups), is it an Engel group?
-- Credit: @marcusbuffett
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- This is a classical slice, not progress on the problem itself. H1 is the case where H and K
-- meet inside the centre of G, which includes the direct product case H ∩ K = 1. There the
-- multiplication map H × K → G/(H ∩ K) is a surjective homomorphism, Engel commutators are
-- computed componentwise in H × K, so G/(H ∩ K) is Engel, and a central kernel adds one more
-- commutator step. H2, the case where H ∩ K is not central, carries the whole open difficulty
-- (the analogue of Fitting's theorem for Engel groups).

namespace OMA.R_Kourovka_1_40_kourovka_1_40_R1

open Kourovka.«1.40»

/-- The product of two normal Engel subgroups that meet inside the centre is Engel. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] (H K : Subgroup G),
    H.Normal → K.Normal → IsEngelGroup H → IsEngelGroup K → H ⊔ K = ⊤ →
    H ⊓ K ≤ Subgroup.center G → IsEngelGroup G

/-- The product of two normal Engel subgroups whose intersection is not central is Engel (open). -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] (H K : Subgroup G),
    H.Normal → K.Normal → IsEngelGroup H → IsEngelGroup K → H ⊔ K = ⊤ →
    ¬ H ⊓ K ≤ Subgroup.center G → IsEngelGroup G

theorem main : H1 → H2 → type_of% @Kourovka.«1.40».kourovka_1_40 := by
  intro h1 h2 G _ H K hH hK hHE hKE hsup
  by_cases hc : H ⊓ K ≤ Subgroup.center G
  · exact h1 G H K hH hK hHE hKE hsup hc
  · exact h2 G H K hH hK hHE hKE hsup hc

end OMA.R_Kourovka_1_40_kourovka_1_40_R1
