import FormalConjectures.Wikipedia.BrocardConjecture
import Mathlib

/-!
# Brocard from eventual Legendre and a twin-prime estimate

Eventual Legendre supplies a distinct prime in each of four successive
unit square intervals once the initial prime gap is at least four.
The residual assertion concerns twin primes only.
-/

namespace OMA.R_Brocard_brocard_conjecture_ferreira_large_n_R2
open Finset Nat Filter

private lemma four_points {p q a b c d : ℕ}
    (ha : a.Prime) (hb : b.Prime) (hc : c.Prime) (hd : d.Prime)
    (lo : p^2<a) (ab : a<b) (bc : b<c) (cd : c<d) (hi : d<q^2) :
    4 ≤ ((Ioo (p^2) (q^2)).filter Nat.Prime).card := by
  have sub : {a,b,c,d} ⊆ (Ioo (p^2) (q^2)).filter Nat.Prime := by
    intro x hx
    simp only [mem_insert,mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> exact mem_filter.mpr ⟨mem_Ioo.mpr ⟨by omega,by omega⟩,by assumption⟩
  have hcard : ({a,b,c,d} : Finset ℕ).card=4 := by
    simp [ab.ne,bc.ne,cd.ne,(ab.trans bc).ne,(bc.trans cd).ne,((ab.trans bc).trans cd).ne]
  exact hcard ▸ card_le_card sub

private theorem spaced {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h3 : 3≤p) (h : p<q) : p+2≤q := by
  have a := hp.odd_of_ne_two (by omega)
  have b := hq.odd_of_ne_two (by omega)
  obtain ⟨u,hu⟩ := a
  obtain ⟨v,hv⟩ := b
  omega


def H1 : Prop := ∀ᶠ m : ℕ in atTop, ∃ r : ℕ, r.Prime ∧ m^2 < r ∧ r < (m+1)^2

def H2 : Prop := ∀ᶠ p : ℕ in atTop, p.Prime → (p+2).Prime →
    4 ≤ ((Ioo (p^2) ((p+2)^2)).filter Nat.Prime).card

theorem main : H1 → H2 → type_of% @Brocard.brocard_conjecture.ferreira_large_n := by
  intro legendre twins
  obtain ⟨L,hL⟩ := eventually_atTop.mp legendre
  obtain ⟨T,hT⟩ := eventually_atTop.mp twins
  apply eventually_atTop.mpr
  refine ⟨max L (max T 3),?_⟩
  intro n hn
  let p := nth Nat.Prime n
  let q := nth Nat.Prime (n+1)
  change 4 ≤ ((Ioo (p^2) (q^2)).filter Nat.Prime).card
  have base : n+2≤p := add_two_le_nth_prime n
  have pp : p.Prime := prime_nth_prime _
  have pq : q.Prime := prime_nth_prime _
  have hq := spaced pp pq (by omega) ((nth_strictMono infinite_setOfPred_prime) (Nat.lt_succ_self n))
  by_cases twin : q = p+2
  · rw [twin]
    exact hT p (by omega) pp (twin ▸ pq)
  have gap : p+4≤q := by
    obtain ⟨u,hu⟩ := pp.odd_of_ne_two (by omega)
    obtain ⟨v,hv⟩ := pq.odd_of_ne_two (by omega)
    omega
  obtain ⟨a,pa,alo,ahi⟩ := hL p (by omega)
  obtain ⟨b,pb,blo,bhi⟩ := hL (p+1) (by omega)
  obtain ⟨c,pc,clo,chi⟩ := hL (p+2) (by omega)
  obtain ⟨d,pd,dlo,dhi⟩ := hL (p+3) (by omega)
  exact four_points pa pb pc pd alo (ahi.trans blo) (bhi.trans clo) (chi.trans dlo)
    (dhi.trans_le (Nat.pow_le_pow_left gap 2))

end OMA.R_Brocard_brocard_conjecture_ferreira_large_n_R2
