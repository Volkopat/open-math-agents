import OMAReductions.R_opg_adams_conjecture_R1

/-!
# Proof of `opg-adams-conjecture.R1.H1`

Proves Ádám's conjecture for tournaments containing a vertex `b` on a directed cycle that has
in-degree 1 or out-degree 1.

- If `b` has unique in-neighbor `a`, reversing `a → b` makes `b` a source (`∀ x, ¬ adj' x b`).
  Every vertex appearing in a directed cycle `l.zip (l.rotate 1)` has both an incoming arc and
  an outgoing arc in the cycle, so no cycle in the reversed tournament can visit `b`, nor can it
  use the new arc `(b, a)`. Hence `cycles (reverse adj a b) ⊆ cycles adj`, and the given cycle
  `C` through `b` is strictly lost.
- Symmetrically, if `b` has unique out-neighbor `c`, reversing `b → c` makes `b` a sink
  (`∀ y, ¬ adj' b y`), so again `cycles (reverse adj b c) ⊂ cycles adj`.
-/

namespace OpgAdamsConjectureR1H1Proof

open OMA.S_opg_adams_conjecture

private lemma mem_zip_rotate_incoming {α : Type*} {l : List α} {p : α × α}
    (hp : p ∈ l.zip (l.rotate 1)) :
    ∃ q ∈ l.zip (l.rotate 1), q.2 = p.1 := by
  rw [List.mem_iff_getElem] at hp
  obtain ⟨i, hi, hpi⟩ := hp
  have hlen_rot : (l.rotate 1).length = l.length := List.length_rotate l 1
  have hlen : (l.zip (l.rotate 1)).length = l.length := by
    rw [List.length_zip, hlen_rot, min_self]
  have hi_l : i < l.length := by omega
  have hpos : 0 < l.length := by omega
  have hp1 : p.1 = l[i]'hi_l := by
    have := congrArg Prod.fst hpi
    simpa [List.getElem_zip] using this.symm
  let j : ℕ := (i + l.length - 1) % l.length
  have hj_l : j < l.length := Nat.mod_lt _ hpos
  have hj_zip : j < (l.zip (l.rotate 1)).length := by omega
  refine ⟨(l.zip (l.rotate 1))[j]'hj_zip, List.getElem_mem hj_zip, ?_⟩
  rw [List.getElem_zip, List.getElem_rotate, hp1]
  dsimp only
  congr 1
  have hmod : (j + 1) % l.length = i := by
    dsimp [j]
    rw [Nat.mod_add_mod]
    have hadd : i + l.length - 1 + 1 = i + l.length := by omega
    rw [hadd, Nat.add_mod_right, Nat.mod_eq_of_lt hi_l]
  exact hmod

private lemma mem_zip_rotate_outgoing {α : Type*} {l : List α} {p : α × α}
    (hp : p ∈ l.zip (l.rotate 1)) :
    ∃ q ∈ l.zip (l.rotate 1), q.1 = p.2 := by
  rw [List.mem_iff_getElem] at hp
  obtain ⟨i, hi, hpi⟩ := hp
  have hlen_rot : (l.rotate 1).length = l.length := List.length_rotate l 1
  have hlen : (l.zip (l.rotate 1)).length = l.length := by
    rw [List.length_zip, hlen_rot, min_self]
  have hi_l : i < l.length := by omega
  have hpos : 0 < l.length := by omega
  have hp2 : p.2 = l[(i + 1) % l.length]'(Nat.mod_lt _ hpos) := by
    have := congrArg Prod.snd hpi
    simpa [List.getElem_zip, List.getElem_rotate] using this.symm
  let j : ℕ := (i + 1) % l.length
  have hj_l : j < l.length := Nat.mod_lt _ hpos
  have hj_zip : j < (l.zip (l.rotate 1)).length := by omega
  refine ⟨(l.zip (l.rotate 1))[j]'hj_zip, List.getElem_mem hj_zip, ?_⟩
  rw [List.getElem_zip, hp2]

end OpgAdamsConjectureR1H1Proof

theorem OMA.solution : OMA.R_opg_adams_conjecture_R1.H1 := by
  open OMA.S_opg_adams_conjecture in
  intro n adj hirr _ _ ⟨b, ⟨C, hC, p, hpC, hpb⟩, hdeg⟩
  rcases hdeg with ⟨a, ha⟩ | ⟨c, hc⟩
  · have hab : adj a b := (ha a).mpr rfl
    have hab_ne : a ≠ b := by
      rintro rfl
      exact hirr a hab
    refine ⟨a, b, hab, ?_⟩
    have hno_in : ∀ x : Fin n, ¬ reverse adj a b x b := by
      intro x hx
      rcases hx with ⟨hxb, hnot⟩ | ⟨rfl, hba⟩
      · exact hnot ⟨(ha x).mp hxb, rfl⟩
      · exact hab_ne hba.symm
    have hsub : cycles (reverse adj a b) ⊆ cycles adj := by
      rintro D ⟨l, hnd, hlen, harcs, rfl⟩
      refine ⟨l, hnd, hlen, fun q hq => ?_, rfl⟩
      rcases harcs q hq with ⟨hqa, _⟩ | ⟨hq1, hq2⟩
      · exact hqa
      · obtain ⟨r, hr, hr2⟩ := OpgAdamsConjectureR1H1Proof.mem_zip_rotate_incoming hq
        have hrb : r.2 = b := hr2.trans hq1
        exact absurd (hrb ▸ harcs r hr) (hno_in r.1)
    have hC_notin : C ∉ cycles (reverse adj a b) := by
      rintro ⟨l, _, _, harcs, hCeq⟩
      rw [hCeq, List.mem_toFinset] at hpC
      obtain ⟨r, hr, hr2⟩ := OpgAdamsConjectureR1H1Proof.mem_zip_rotate_incoming hpC
      have hrb : r.2 = b := hr2.trans hpb
      exact hno_in r.1 (hrb ▸ harcs r hr)
    have hssub : cycles (reverse adj a b) ⊂ cycles adj :=
      Set.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hC_notin (heq ▸ hC)⟩
    exact Set.ncard_lt_ncard hssub (Set.toFinite _)
  · have hbc : adj b c := (hc c).mpr rfl
    have hbc_ne : b ≠ c := by
      rintro rfl
      exact hirr b hbc
    refine ⟨b, c, hbc, ?_⟩
    have hno_out : ∀ y : Fin n, ¬ reverse adj b c b y := by
      intro y hy
      rcases hy with ⟨hby, hnot⟩ | ⟨hcb, rfl⟩
      · exact hnot ⟨rfl, (hc y).mp hby⟩
      · exact hbc_ne hcb
    have hsub : cycles (reverse adj b c) ⊆ cycles adj := by
      rintro D ⟨l, hnd, hlen, harcs, rfl⟩
      refine ⟨l, hnd, hlen, fun q hq => ?_, rfl⟩
      rcases harcs q hq with ⟨hqa, _⟩ | ⟨hq1, hq2⟩
      · exact hqa
      · obtain ⟨r, hr, hr1⟩ := OpgAdamsConjectureR1H1Proof.mem_zip_rotate_outgoing hq
        have hrb : r.1 = b := hr1.trans hq2
        exact absurd (hrb ▸ harcs r hr) (hno_out r.2)
    have hC_notin : C ∉ cycles (reverse adj b c) := by
      rintro ⟨l, _, _, harcs, hCeq⟩
      rw [hCeq, List.mem_toFinset] at hpC
      exact hno_out p.2 (hpb ▸ harcs p hpC)
    have hssub : cycles (reverse adj b c) ⊂ cycles adj :=
      Set.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq => hC_notin (heq ▸ hC)⟩
    exact Set.ncard_lt_ncard hssub (Set.toFinite _)
