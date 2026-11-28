import OMAReductions.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1
import Mathlib.Combinatorics.SimpleGraph.Bipartite

/-! Maximum-cut reduction of Dean's conjecture for k = 6 to the k = 3 case on
bipartite graphs. Any finite graph with minimum degree at least 6 admits a
bipartite spanning subgraph with minimum degree at least 3 (H1). Every cycle
in a bipartite graph has even length, so a cycle of length divisible by 3 (H2)
has length divisible by 6. -/

namespace OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1_H1_R1

open SimpleGraph

def H1 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj],
    6 ≤ G.minDegree →
      ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
        H ≤ G ∧ H.IsBipartite ∧ 3 ≤ H.minDegree

def H2 : Prop :=
  ∀ {V : Type} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) [DecidableRel H.Adj],
    H.IsBipartite → 3 ≤ H.minDegree → ∃ m ∈ H.cycleLengths, 3 ∣ m

lemma even_walk_of_coloring {V : Type} {H : SimpleGraph V}
    (c : V → Fin 2) (hc : ∀ ⦃u v⦄, H.Adj u v → c u ≠ c v) :
    ∀ {u v : V} (p : H.Walk u v),
      (Even p.length ↔ c u = c v) := by
  intro u v p
  induction p with
  | nil => simp
  | @cons u w v hadj p ih =>
    simp only [Walk.length_cons, Nat.even_add_one, ih]
    have hne : c u ≠ c w := hc hadj
    generalize hcu : c u = xu
    generalize hcw : c w = xw
    generalize hcv : c v = xv
    fin_cases xu <;> fin_cases xw <;> fin_cases xv <;> simp_all

lemma cycleLengths_mono {V : Type} {H G : SimpleGraph V} (hHG : H ≤ G)
    {m : ℕ} (hm : m ∈ H.cycleLengths) : m ∈ G.cycleLengths := by
  rcases hm with ⟨v, c, hc, rfl⟩
  exact ⟨v, c.mapLe hHG, hc.mapLe hHG, by simp⟩

theorem main : H1 → H2 →
    OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1.H1 := by
  intro hmax hthree V _ _ G _ _ hdeg
  obtain ⟨H, _, hle, hbip, hmin⟩ := hmax G hdeg
  obtain ⟨m, hm, hdvd3⟩ := hthree H hbip hmin
  have hdvd2 : 2 ∣ m := by
    rcases hm with ⟨v, c, _, rfl⟩
    obtain ⟨f⟩ := hbip
    have hev : Even c.length := (even_walk_of_coloring f (fun _ _ hadj => f.valid hadj) c).mpr rfl
    exact even_iff_two_dvd.mp hev
  have hdvd6 : 6 ∣ m := by
    have hcop : Nat.Coprime 2 3 := by decide
    exact hcop.mul_dvd_of_dvd_of_dvd hdvd2 hdvd3
  exact ⟨m, cycleLengths_mono hle hm, hdvd6⟩

end OMA.R_Arxiv_2605_02731_dean_conjecture_variants_six_le_R1_H1_R1_H1_R1
