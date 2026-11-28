import OMAStatements.S_oeis_a229506

namespace OMA.P_oeis_a229506

open OMA.S_oeis_a229506

private def encW (v : Fin 4 → Fin 3) : Fin 81 :=
  ⟨(v 0).1 + (v 1).1 * 3 + (v 2).1 * 9 + (v 3).1 * 27,
   by have := (v 0).2; have := (v 1).2; have := (v 2).2; have := (v 3).2; omega⟩

private def decW (x : Fin 81) (c : Fin 4) : Fin 3 :=
  ⟨(x.1 / 3 ^ c.1) % 3, Nat.mod_lt _ (by omega)⟩

private lemma decW_encW (v : Fin 4 → Fin 3) : decW (encW v) = v := by
  funext c; fin_cases c <;> (apply Fin.ext; unfold decW encW; dsimp; have := (v 0).2; have := (v 1).2; have := (v 2).2; have := (v 3).2; omega)

private lemma encW_decW : ∀ x : Fin 81, encW (decW x) = x := by decide

private def rowTypeVal (x : Fin 81) : ℕ :=
  (if x.1 < 40 then (if x.1 < 20 then (if x.1 < 10 then (if x.1 < 5 then (if x.1 < 2 then (if x.1 < 1 then 0 else 9) else (if x.1 < 3 then 9 else (if x.1 < 4 then 5 else 3))) else (if x.1 < 7 then (if x.1 < 6 then 13 else 5) else (if x.1 < 8 then 13 else (if x.1 < 9 then 3 else 2)))) else (if x.1 < 15 then (if x.1 < 12 then (if x.1 < 11 then 6 else 12) else (if x.1 < 13 then 8 else (if x.1 < 14 then 1 else 10))) else (if x.1 < 17 then (if x.1 < 16 then 11 else 7) else (if x.1 < 18 then 4 else (if x.1 < 19 then 2 else 12))))) else (if x.1 < 30 then (if x.1 < 25 then (if x.1 < 22 then (if x.1 < 21 then 6 else 11) else (if x.1 < 23 then 4 else (if x.1 < 24 then 7 else 8))) else (if x.1 < 27 then (if x.1 < 26 then 10 else 1) else (if x.1 < 28 then 1 else (if x.1 < 29 then 8 else 10)))) else (if x.1 < 35 then (if x.1 < 32 then (if x.1 < 31 then 6 else 2) else (if x.1 < 33 then 12 else (if x.1 < 34 then 7 else 11))) else (if x.1 < 37 then (if x.1 < 36 then 4 else 3) else (if x.1 < 38 then 5 else (if x.1 < 39 then 13 else 9)))))) else (if x.1 < 60 then (if x.1 < 50 then (if x.1 < 45 then (if x.1 < 42 then (if x.1 < 41 then 0 else 9) else (if x.1 < 43 then 13 else (if x.1 < 44 then 5 else 3))) else (if x.1 < 47 then (if x.1 < 46 then 4 else 11) else (if x.1 < 48 then 7 else (if x.1 < 49 then 12 else 2)))) else (if x.1 < 55 then (if x.1 < 52 then (if x.1 < 51 then 6 else 10) else (if x.1 < 53 then 8 else (if x.1 < 54 then 1 else 1))) else (if x.1 < 57 then (if x.1 < 56 then 10 else 8) else (if x.1 < 58 then 7 else (if x.1 < 59 then 4 else 11))))) else (if x.1 < 70 then (if x.1 < 65 then (if x.1 < 62 then (if x.1 < 61 then 6 else 12) else (if x.1 < 63 then 2 else (if x.1 < 64 then 4 else 7))) else (if x.1 < 67 then (if x.1 < 66 then 11 else 10) else (if x.1 < 68 then 1 else (if x.1 < 69 then 8 else 12)))) else (if x.1 < 75 then (if x.1 < 72 then (if x.1 < 71 then 6 else 2) else (if x.1 < 73 then 3 else (if x.1 < 74 then 13 else 5))) else (if x.1 < 78 then (if x.1 < 76 then 13 else (if x.1 < 77 then 3 else 5)) else (if x.1 < 79 then 9 else (if x.1 < 80 then 9 else 0)))))))

private lemma rowTypeVal_lt : ∀ x : Fin 81, rowTypeVal x < 14 := by decide

private def rowType (v : Fin 4 → Fin 3) : Fin 14 :=
  ⟨rowTypeVal (encW v), rowTypeVal_lt (encW v)⟩

private def stepErr (p v : Fin 4 → Fin 3) : ℕ :=
  (∑ c : Fin 3, if p ⟨c.1, by omega⟩ = v ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 3, if p ⟨c.1 + 1, by omega⟩ = v ⟨c.1, by omega⟩ then 1 else 0)

private def multVal (pt nt : Fin 14) (de : Fin 2) : ℕ :=
  match pt.1 with
  | 0 => match nt.1 with
    | 0 => match de.1 with | 0 => 2 | _ => 0
    | 1 => match de.1 with | 0 => 2 | _ => 2
    | 2 => match de.1 with | 0 => 2 | _ => 0
    | 3 => match de.1 with | 0 => 2 | _ => 0
    | 4 => match de.1 with | 0 => 0 | _ => 2
    | 5 => match de.1 with | 0 => 2 | _ => 0
    | 6 => match de.1 with | 0 => 2 | _ => 0
    | 7 => match de.1 with | 0 => 0 | _ => 2
    | 8 => match de.1 with | 0 => 2 | _ => 0
    | 9 => match de.1 with | 0 => 2 | _ => 2
    | 10 => match de.1 with | 0 => 0 | _ => 4
    | 11 => match de.1 with | 0 => 0 | _ => 0
    | 12 => match de.1 with | 0 => 0 | _ => 2
    | 13 => match de.1 with | 0 => 0 | _ => 2
    | _ => 0
  | 1 => match nt.1 with
    | 0 => match de.1 with | 0 => 1 | _ => 1
    | 1 => match de.1 with | 0 => 1 | _ => 2
    | 2 => match de.1 with | 0 => 1 | _ => 3
    | 3 => match de.1 with | 0 => 1 | _ => 1
    | 4 => match de.1 with | 0 => 0 | _ => 3
    | 5 => match de.1 with | 0 => 1 | _ => 1
    | 6 => match de.1 with | 0 => 1 | _ => 1
    | 7 => match de.1 with | 0 => 0 | _ => 1
    | 8 => match de.1 with | 0 => 1 | _ => 1
    | 9 => match de.1 with | 0 => 1 | _ => 2
    | 10 => match de.1 with | 0 => 0 | _ => 2
    | 11 => match de.1 with | 0 => 0 | _ => 2
    | 12 => match de.1 with | 0 => 0 | _ => 3
    | 13 => match de.1 with | 0 => 0 | _ => 1
    | _ => 0
  | 2 => match nt.1 with
    | 0 => match de.1 with | 0 => 1 | _ => 0
    | 1 => match de.1 with | 0 => 1 | _ => 3
    | 2 => match de.1 with | 0 => 1 | _ => 0
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 1 | _ => 1
    | 5 => match de.1 with | 0 => 0 | _ => 3
    | 6 => match de.1 with | 0 => 1 | _ => 2
    | 7 => match de.1 with | 0 => 1 | _ => 2
    | 8 => match de.1 with | 0 => 0 | _ => 3
    | 9 => match de.1 with | 0 => 1 | _ => 1
    | 10 => match de.1 with | 0 => 1 | _ => 1
    | 11 => match de.1 with | 0 => 0 | _ => 2
    | 12 => match de.1 with | 0 => 0 | _ => 3
    | 13 => match de.1 with | 0 => 0 | _ => 1
    | _ => 0
  | 3 => match nt.1 with
    | 0 => match de.1 with | 0 => 1 | _ => 0
    | 1 => match de.1 with | 0 => 1 | _ => 1
    | 2 => match de.1 with | 0 => 0 | _ => 2
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 0 | _ => 2
    | 5 => match de.1 with | 0 => 0 | _ => 2
    | 6 => match de.1 with | 0 => 0 | _ => 2
    | 7 => match de.1 with | 0 => 0 | _ => 2
    | 8 => match de.1 with | 0 => 0 | _ => 2
    | 9 => match de.1 with | 0 => 1 | _ => 1
    | 10 => match de.1 with | 0 => 1 | _ => 0
    | 11 => match de.1 with | 0 => 0 | _ => 0
    | 12 => match de.1 with | 0 => 0 | _ => 2
    | 13 => match de.1 with | 0 => 0 | _ => 2
    | _ => 0
  | 4 => match nt.1 with
    | 0 => match de.1 with | 0 => 0 | _ => 1
    | 1 => match de.1 with | 0 => 0 | _ => 3
    | 2 => match de.1 with | 0 => 1 | _ => 1
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 1 | _ => 0
    | 5 => match de.1 with | 0 => 0 | _ => 1
    | 6 => match de.1 with | 0 => 1 | _ => 1
    | 7 => match de.1 with | 0 => 1 | _ => 1
    | 8 => match de.1 with | 0 => 0 | _ => 1
    | 9 => match de.1 with | 0 => 0 | _ => 1
    | 10 => match de.1 with | 0 => 0 | _ => 2
    | 11 => match de.1 with | 0 => 0 | _ => 2
    | 12 => match de.1 with | 0 => 0 | _ => 3
    | 13 => match de.1 with | 0 => 0 | _ => 1
    | _ => 0
  | 5 => match nt.1 with
    | 0 => match de.1 with | 0 => 1 | _ => 0
    | 1 => match de.1 with | 0 => 1 | _ => 1
    | 2 => match de.1 with | 0 => 0 | _ => 3
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 0 | _ => 1
    | 5 => match de.1 with | 0 => 1 | _ => 0
    | 6 => match de.1 with | 0 => 1 | _ => 2
    | 7 => match de.1 with | 0 => 0 | _ => 3
    | 8 => match de.1 with | 0 => 0 | _ => 3
    | 9 => match de.1 with | 0 => 1 | _ => 3
    | 10 => match de.1 with | 0 => 1 | _ => 1
    | 11 => match de.1 with | 0 => 0 | _ => 2
    | 12 => match de.1 with | 0 => 1 | _ => 2
    | 13 => match de.1 with | 0 => 1 | _ => 1
    | _ => 0
  | 6 => match nt.1 with
    | 0 => match de.1 with | 0 => 1 | _ => 0
    | 1 => match de.1 with | 0 => 1 | _ => 1
    | 2 => match de.1 with | 0 => 1 | _ => 2
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 1 | _ => 1
    | 5 => match de.1 with | 0 => 1 | _ => 2
    | 6 => match de.1 with | 0 => 3 | _ => 0
    | 7 => match de.1 with | 0 => 2 | _ => 1
    | 8 => match de.1 with | 0 => 0 | _ => 2
    | 9 => match de.1 with | 0 => 1 | _ => 1
    | 10 => match de.1 with | 0 => 1 | _ => 0
    | 11 => match de.1 with | 0 => 1 | _ => 2
    | 12 => match de.1 with | 0 => 2 | _ => 1
    | 13 => match de.1 with | 0 => 1 | _ => 1
    | _ => 0
  | 7 => match nt.1 with
    | 0 => match de.1 with | 0 => 0 | _ => 1
    | 1 => match de.1 with | 0 => 0 | _ => 1
    | 2 => match de.1 with | 0 => 1 | _ => 2
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 1 | _ => 1
    | 5 => match de.1 with | 0 => 0 | _ => 3
    | 6 => match de.1 with | 0 => 2 | _ => 1
    | 7 => match de.1 with | 0 => 2 | _ => 0
    | 8 => match de.1 with | 0 => 0 | _ => 1
    | 9 => match de.1 with | 0 => 0 | _ => 3
    | 10 => match de.1 with | 0 => 0 | _ => 2
    | 11 => match de.1 with | 0 => 1 | _ => 1
    | 12 => match de.1 with | 0 => 1 | _ => 3
    | 13 => match de.1 with | 0 => 0 | _ => 3
    | _ => 0
  | 8 => match nt.1 with
    | 0 => match de.1 with | 0 => 1 | _ => 0
    | 1 => match de.1 with | 0 => 1 | _ => 1
    | 2 => match de.1 with | 0 => 0 | _ => 3
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 0 | _ => 1
    | 5 => match de.1 with | 0 => 0 | _ => 3
    | 6 => match de.1 with | 0 => 0 | _ => 2
    | 7 => match de.1 with | 0 => 0 | _ => 1
    | 8 => match de.1 with | 0 => 1 | _ => 0
    | 9 => match de.1 with | 0 => 1 | _ => 1
    | 10 => match de.1 with | 0 => 0 | _ => 2
    | 11 => match de.1 with | 0 => 0 | _ => 2
    | 12 => match de.1 with | 0 => 0 | _ => 1
    | 13 => match de.1 with | 0 => 0 | _ => 1
    | _ => 0
  | 9 => match nt.1 with
    | 0 => match de.1 with | 0 => 1 | _ => 1
    | 1 => match de.1 with | 0 => 1 | _ => 2
    | 2 => match de.1 with | 0 => 1 | _ => 1
    | 3 => match de.1 with | 0 => 1 | _ => 1
    | 4 => match de.1 with | 0 => 0 | _ => 1
    | 5 => match de.1 with | 0 => 1 | _ => 3
    | 6 => match de.1 with | 0 => 1 | _ => 1
    | 7 => match de.1 with | 0 => 0 | _ => 3
    | 8 => match de.1 with | 0 => 1 | _ => 1
    | 9 => match de.1 with | 0 => 1 | _ => 2
    | 10 => match de.1 with | 0 => 0 | _ => 2
    | 11 => match de.1 with | 0 => 0 | _ => 2
    | 12 => match de.1 with | 0 => 0 | _ => 1
    | 13 => match de.1 with | 0 => 0 | _ => 3
    | _ => 0
  | 10 => match nt.1 with
    | 0 => match de.1 with | 0 => 0 | _ => 2
    | 1 => match de.1 with | 0 => 0 | _ => 2
    | 2 => match de.1 with | 0 => 1 | _ => 1
    | 3 => match de.1 with | 0 => 1 | _ => 0
    | 4 => match de.1 with | 0 => 0 | _ => 2
    | 5 => match de.1 with | 0 => 1 | _ => 1
    | 6 => match de.1 with | 0 => 1 | _ => 0
    | 7 => match de.1 with | 0 => 0 | _ => 2
    | 8 => match de.1 with | 0 => 0 | _ => 2
    | 9 => match de.1 with | 0 => 0 | _ => 2
    | 10 => match de.1 with | 0 => 0 | _ => 0
    | 11 => match de.1 with | 0 => 0 | _ => 2
    | 12 => match de.1 with | 0 => 0 | _ => 2
    | 13 => match de.1 with | 0 => 0 | _ => 2
    | _ => 0
  | 11 => match nt.1 with
    | 0 => match de.1 with | 0 => 0 | _ => 0
    | 1 => match de.1 with | 0 => 0 | _ => 2
    | 2 => match de.1 with | 0 => 0 | _ => 2
    | 3 => match de.1 with | 0 => 0 | _ => 0
    | 4 => match de.1 with | 0 => 0 | _ => 2
    | 5 => match de.1 with | 0 => 0 | _ => 2
    | 6 => match de.1 with | 0 => 1 | _ => 2
    | 7 => match de.1 with | 0 => 1 | _ => 1
    | 8 => match de.1 with | 0 => 0 | _ => 2
    | 9 => match de.1 with | 0 => 0 | _ => 2
    | 10 => match de.1 with | 0 => 0 | _ => 2
    | 11 => match de.1 with | 0 => 1 | _ => 0
    | 12 => match de.1 with | 0 => 1 | _ => 1
    | 13 => match de.1 with | 0 => 0 | _ => 2
    | _ => 0
  | 12 => match nt.1 with
    | 0 => match de.1 with | 0 => 0 | _ => 1
    | 1 => match de.1 with | 0 => 0 | _ => 3
    | 2 => match de.1 with | 0 => 0 | _ => 3
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 0 | _ => 3
    | 5 => match de.1 with | 0 => 1 | _ => 2
    | 6 => match de.1 with | 0 => 2 | _ => 1
    | 7 => match de.1 with | 0 => 1 | _ => 3
    | 8 => match de.1 with | 0 => 0 | _ => 1
    | 9 => match de.1 with | 0 => 0 | _ => 1
    | 10 => match de.1 with | 0 => 0 | _ => 2
    | 11 => match de.1 with | 0 => 1 | _ => 1
    | 12 => match de.1 with | 0 => 2 | _ => 0
    | 13 => match de.1 with | 0 => 1 | _ => 1
    | _ => 0
  | 13 => match nt.1 with
    | 0 => match de.1 with | 0 => 0 | _ => 1
    | 1 => match de.1 with | 0 => 0 | _ => 1
    | 2 => match de.1 with | 0 => 0 | _ => 1
    | 3 => match de.1 with | 0 => 0 | _ => 2
    | 4 => match de.1 with | 0 => 0 | _ => 1
    | 5 => match de.1 with | 0 => 1 | _ => 1
    | 6 => match de.1 with | 0 => 1 | _ => 1
    | 7 => match de.1 with | 0 => 0 | _ => 3
    | 8 => match de.1 with | 0 => 0 | _ => 1
    | 9 => match de.1 with | 0 => 0 | _ => 3
    | 10 => match de.1 with | 0 => 0 | _ => 2
    | 11 => match de.1 with | 0 => 0 | _ => 2
    | 12 => match de.1 with | 0 => 1 | _ => 1
    | 13 => match de.1 with | 0 => 1 | _ => 0
    | _ => 0
  | _ => 0

private def base1Val (t : Fin 14) (err : ℕ) : ℕ :=
  match t.1 with
  | 0 => (if err < 1 then 3 else 0)
  | 1 => (if err < 1 then 6 else 0)
  | 2 => (if err < 1 then 6 else 0)
  | 3 => (if err < 1 then 6 else 0)
  | 4 => (if err < 1 then 6 else 0)
  | 5 => (if err < 1 then 6 else 0)
  | 6 => (if err < 1 then 6 else 0)
  | 7 => (if err < 1 then 6 else 0)
  | 8 => (if err < 1 then 6 else 0)
  | 9 => (if err < 1 then 6 else 0)
  | 10 => (if err < 1 then 6 else 0)
  | 11 => (if err < 1 then 6 else 0)
  | 12 => (if err < 1 then 6 else 0)
  | 13 => (if err < 1 then 6 else 0)
  | _ => 0

private def dp : ℕ → Fin 14 → ℕ → ℕ
  | 0, _, _ => 0
  | 1, t, err => base1Val t err
  | n + 1, nt, err =>
    if herr : err ≤ 1 then
      ∑ pt : Fin 14, ∑ pe : Fin (err + 1),
        dp n pt pe.1 * multVal pt nt ⟨err - pe.1, by omega⟩
    else 0

private lemma dp_succ_eq (n : ℕ) (hn : 1 ≤ n) (nt : Fin 14) (err : ℕ) (herr : err ≤ 1) :
    dp (n + 1) nt err = ∑ pt : Fin 14, ∑ pe : Fin (err + 1),
      dp n pt pe.1 * multVal pt nt ⟨err - pe.1, by omega⟩ := by
  cases n with
  | zero => omega
  | succ k => simp [dp, herr]

private lemma sum_fin_T (f : Fin 14 → ℕ) :
    (∑ t : Fin 14, f t) = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ + f ⟨3, by omega⟩ + f ⟨4, by omega⟩ + f ⟨5, by omega⟩ + f ⟨6, by omega⟩ + f ⟨7, by omega⟩ + f ⟨8, by omega⟩ + f ⟨9, by omega⟩ + f ⟨10, by omega⟩ + f ⟨11, by omega⟩ + f ⟨12, by omega⟩ + f ⟨13, by omega⟩ := by
  rw [Fin.sum_univ_def]; simp [List.finRange]; ring

private def dpInv (m : ℕ) : Prop :=
    dp (m + 3) ⟨0, by omega⟩ 0 = 432 * 9 ^ m ∧
    dp (m + 3) ⟨0, by omega⟩ 1 = (768 * m + 1296) * 9 ^ m ∧
    dp (m + 3) ⟨1, by omega⟩ 0 = 432 * 9 ^ m ∧
    dp (m + 3) ⟨1, by omega⟩ 1 = (768 * m + 2016) * 9 ^ m ∧
    dp (m + 3) ⟨2, by omega⟩ 0 = 432 * 9 ^ m ∧
    dp (m + 3) ⟨2, by omega⟩ 1 = (768 * m + 2016) * 9 ^ m ∧
    dp (m + 3) ⟨3, by omega⟩ 0 = 216 * 9 ^ m ∧
    dp (m + 3) ⟨3, by omega⟩ 1 = (384 * m + 1368) * 9 ^ m ∧
    dp (m + 3) ⟨4, by omega⟩ 0 = 216 * 9 ^ m ∧
    dp (m + 3) ⟨4, by omega⟩ 1 = (384 * m + 1368) * 9 ^ m ∧
    dp (m + 3) ⟨5, by omega⟩ 0 = 432 * 9 ^ m ∧
    dp (m + 3) ⟨5, by omega⟩ 1 = (768 * m + 2016) * 9 ^ m ∧
    dp (m + 3) ⟨6, by omega⟩ 0 = 864 * 9 ^ m ∧
    dp (m + 3) ⟨6, by omega⟩ 1 = (1536 * m + 2592) * 9 ^ m ∧
    dp (m + 3) ⟨7, by omega⟩ 0 = 432 * 9 ^ m ∧
    dp (m + 3) ⟨7, by omega⟩ 1 = (768 * m + 2016) * 9 ^ m ∧
    dp (m + 3) ⟨8, by omega⟩ 0 = 216 * 9 ^ m ∧
    dp (m + 3) ⟨8, by omega⟩ 1 = (384 * m + 1368) * 9 ^ m ∧
    dp (m + 3) ⟨9, by omega⟩ 0 = 432 * 9 ^ m ∧
    dp (m + 3) ⟨9, by omega⟩ 1 = (768 * m + 2016) * 9 ^ m ∧
    dp (m + 3) ⟨10, by omega⟩ 0 = 216 * 9 ^ m ∧
    dp (m + 3) ⟨10, by omega⟩ 1 = (384 * m + 1368) * 9 ^ m ∧
    dp (m + 3) ⟨11, by omega⟩ 0 = 216 * 9 ^ m ∧
    dp (m + 3) ⟨11, by omega⟩ 1 = (384 * m + 1368) * 9 ^ m ∧
    dp (m + 3) ⟨12, by omega⟩ 0 = 432 * 9 ^ m ∧
    dp (m + 3) ⟨12, by omega⟩ 1 = (768 * m + 2016) * 9 ^ m ∧
    dp (m + 3) ⟨13, by omega⟩ 0 = 216 * 9 ^ m ∧
    dp (m + 3) ⟨13, by omega⟩ 1 = (384 * m + 1368) * 9 ^ m

private lemma dp_base_0_0 :
    dp (0 + 3) ⟨0, by omega⟩ 0 = 432 * 9 ^ 0 := by decide

private lemma dp_step_0_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨0, by omega⟩ 0 = 432 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_0_1 :
    dp (0 + 3) ⟨0, by omega⟩ 1 = (768 * 0 + 1296) * 9 ^ 0 := by decide

private lemma dp_step_0_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨0, by omega⟩ 1 = (768 * (m + 1) + 1296) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_1_0 :
    dp (0 + 3) ⟨1, by omega⟩ 0 = 432 * 9 ^ 0 := by decide

private lemma dp_step_1_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨1, by omega⟩ 0 = 432 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_1_1 :
    dp (0 + 3) ⟨1, by omega⟩ 1 = (768 * 0 + 2016) * 9 ^ 0 := by decide

private lemma dp_step_1_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨1, by omega⟩ 1 = (768 * (m + 1) + 2016) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_2_0 :
    dp (0 + 3) ⟨2, by omega⟩ 0 = 432 * 9 ^ 0 := by decide

private lemma dp_step_2_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨2, by omega⟩ 0 = 432 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_2_1 :
    dp (0 + 3) ⟨2, by omega⟩ 1 = (768 * 0 + 2016) * 9 ^ 0 := by decide

private lemma dp_step_2_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨2, by omega⟩ 1 = (768 * (m + 1) + 2016) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_3_0 :
    dp (0 + 3) ⟨3, by omega⟩ 0 = 216 * 9 ^ 0 := by decide

private lemma dp_step_3_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨3, by omega⟩ 0 = 216 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_3_1 :
    dp (0 + 3) ⟨3, by omega⟩ 1 = (384 * 0 + 1368) * 9 ^ 0 := by decide

private lemma dp_step_3_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨3, by omega⟩ 1 = (384 * (m + 1) + 1368) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_4_0 :
    dp (0 + 3) ⟨4, by omega⟩ 0 = 216 * 9 ^ 0 := by decide

private lemma dp_step_4_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨4, by omega⟩ 0 = 216 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_4_1 :
    dp (0 + 3) ⟨4, by omega⟩ 1 = (384 * 0 + 1368) * 9 ^ 0 := by decide

private lemma dp_step_4_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨4, by omega⟩ 1 = (384 * (m + 1) + 1368) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_5_0 :
    dp (0 + 3) ⟨5, by omega⟩ 0 = 432 * 9 ^ 0 := by decide

private lemma dp_step_5_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨5, by omega⟩ 0 = 432 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_5_1 :
    dp (0 + 3) ⟨5, by omega⟩ 1 = (768 * 0 + 2016) * 9 ^ 0 := by decide

private lemma dp_step_5_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨5, by omega⟩ 1 = (768 * (m + 1) + 2016) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_6_0 :
    dp (0 + 3) ⟨6, by omega⟩ 0 = 864 * 9 ^ 0 := by decide

private lemma dp_step_6_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨6, by omega⟩ 0 = 864 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_6_1 :
    dp (0 + 3) ⟨6, by omega⟩ 1 = (1536 * 0 + 2592) * 9 ^ 0 := by decide

private lemma dp_step_6_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨6, by omega⟩ 1 = (1536 * (m + 1) + 2592) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_7_0 :
    dp (0 + 3) ⟨7, by omega⟩ 0 = 432 * 9 ^ 0 := by decide

private lemma dp_step_7_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨7, by omega⟩ 0 = 432 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_7_1 :
    dp (0 + 3) ⟨7, by omega⟩ 1 = (768 * 0 + 2016) * 9 ^ 0 := by decide

private lemma dp_step_7_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨7, by omega⟩ 1 = (768 * (m + 1) + 2016) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_8_0 :
    dp (0 + 3) ⟨8, by omega⟩ 0 = 216 * 9 ^ 0 := by decide

private lemma dp_step_8_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨8, by omega⟩ 0 = 216 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_8_1 :
    dp (0 + 3) ⟨8, by omega⟩ 1 = (384 * 0 + 1368) * 9 ^ 0 := by decide

private lemma dp_step_8_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨8, by omega⟩ 1 = (384 * (m + 1) + 1368) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_9_0 :
    dp (0 + 3) ⟨9, by omega⟩ 0 = 432 * 9 ^ 0 := by decide

private lemma dp_step_9_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨9, by omega⟩ 0 = 432 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_9_1 :
    dp (0 + 3) ⟨9, by omega⟩ 1 = (768 * 0 + 2016) * 9 ^ 0 := by decide

private lemma dp_step_9_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨9, by omega⟩ 1 = (768 * (m + 1) + 2016) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_10_0 :
    dp (0 + 3) ⟨10, by omega⟩ 0 = 216 * 9 ^ 0 := by decide

private lemma dp_step_10_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨10, by omega⟩ 0 = 216 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_10_1 :
    dp (0 + 3) ⟨10, by omega⟩ 1 = (384 * 0 + 1368) * 9 ^ 0 := by decide

private lemma dp_step_10_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨10, by omega⟩ 1 = (384 * (m + 1) + 1368) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_11_0 :
    dp (0 + 3) ⟨11, by omega⟩ 0 = 216 * 9 ^ 0 := by decide

private lemma dp_step_11_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨11, by omega⟩ 0 = 216 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_11_1 :
    dp (0 + 3) ⟨11, by omega⟩ 1 = (384 * 0 + 1368) * 9 ^ 0 := by decide

private lemma dp_step_11_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨11, by omega⟩ 1 = (384 * (m + 1) + 1368) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_12_0 :
    dp (0 + 3) ⟨12, by omega⟩ 0 = 432 * 9 ^ 0 := by decide

private lemma dp_step_12_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨12, by omega⟩ 0 = 432 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_12_1 :
    dp (0 + 3) ⟨12, by omega⟩ 1 = (768 * 0 + 2016) * 9 ^ 0 := by decide

private lemma dp_step_12_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨12, by omega⟩ 1 = (768 * (m + 1) + 2016) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_base_13_0 :
    dp (0 + 3) ⟨13, by omega⟩ 0 = 216 * 9 ^ 0 := by decide

private lemma dp_step_13_0 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨13, by omega⟩ 0 = 216 * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, _, h2, _, h4, _, h6, _, h8, _, h10, _, h12, _, h14, _, h16, _, h18, _, h20, _, h22, _, h24, _, h26, _⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h2, h4, h6, h8, h10, h12, h14, h16, h18, h20, h22, h24, h26]
  ring

private lemma dp_base_13_1 :
    dp (0 + 3) ⟨13, by omega⟩ 1 = (384 * 0 + 1368) * 9 ^ 0 := by decide

private lemma dp_step_13_1 (m : ℕ) (ih : dpInv m) :
    dp (m + 1 + 3) ⟨13, by omega⟩ 1 = (384 * (m + 1) + 1368) * 9 ^ (m + 1) := by
  unfold dpInv at ih
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27⟩ := ih
  rw [show m + 1 + 3 = (m + 3) + 1 by omega, dp_succ_eq _ (by omega) _ _ (by omega), sum_fin_T]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Fin.val_succ, Nat.reduceSub, Nat.reduceAdd, multVal]
  rw [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27]
  ring

private lemma dp_closed (m : ℕ) : dpInv m := by
  induction m with
  | zero => exact ⟨dp_base_0_0, dp_base_0_1, dp_base_1_0, dp_base_1_1, dp_base_2_0, dp_base_2_1, dp_base_3_0, dp_base_3_1, dp_base_4_0, dp_base_4_1, dp_base_5_0, dp_base_5_1, dp_base_6_0, dp_base_6_1, dp_base_7_0, dp_base_7_1, dp_base_8_0, dp_base_8_1, dp_base_9_0, dp_base_9_1, dp_base_10_0, dp_base_10_1, dp_base_11_0, dp_base_11_1, dp_base_12_0, dp_base_12_1, dp_base_13_0, dp_base_13_1⟩
  | succ m ih => exact ⟨dp_step_0_0 m ih, dp_step_0_1 m ih, dp_step_1_0 m ih, dp_step_1_1 m ih, dp_step_2_0 m ih, dp_step_2_1 m ih, dp_step_3_0 m ih, dp_step_3_1 m ih, dp_step_4_0 m ih, dp_step_4_1 m ih, dp_step_5_0 m ih, dp_step_5_1 m ih, dp_step_6_0 m ih, dp_step_6_1 m ih, dp_step_7_0 m ih, dp_step_7_1 m ih, dp_step_8_0 m ih, dp_step_8_1 m ih, dp_step_9_0 m ih, dp_step_9_1 m ih, dp_step_10_0 m ih, dp_step_10_1 m ih, dp_step_11_0 m ih, dp_step_11_1 m ih, dp_step_12_0 m ih, dp_step_12_1 m ih, dp_step_13_0 m ih, dp_step_13_1 m ih⟩

private lemma mistakes_succ (n : ℕ) (hn : 1 ≤ n) (A : Fin (n + 1) → Fin 4 → Fin 3) :
    mistakes (n + 1) A = mistakes n (fun r => A r.castSucc) +
      stepErr (A ⟨n - 1, by omega⟩) (A (Fin.last n)) := by
  unfold mistakes stepErr
  
  have h2 : (∑ r : Fin (n + 1 - 1), ((∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩ then 1 else 0))) =
      (∑ r : Fin (n - 1), ((∑ c : Fin 3, if A (⟨r.1, by omega⟩ : Fin n).castSucc ⟨c.1, by omega⟩ = A (⟨r.1 + 1, by omega⟩ : Fin n).castSucc ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 3, if A (⟨r.1, by omega⟩ : Fin n).castSucc ⟨c.1 + 1, by omega⟩ = A (⟨r.1 + 1, by omega⟩ : Fin n).castSucc ⟨c.1, by omega⟩ then 1 else 0))) +
      (((∑ c : Fin 3, if A ⟨n - 1, by omega⟩ ⟨c.1, by omega⟩ = A (Fin.last n) ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 3, if A ⟨n - 1, by omega⟩ ⟨c.1 + 1, by omega⟩ = A (Fin.last n) ⟨c.1, by omega⟩ then 1 else 0))) := by
    have heq_n : n + 1 - 1 = (n - 1) + 1 := by omega
    rw [show (∑ r : Fin (n + 1 - 1), ((∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩ then 1 else 0))) = ∑ r : Fin ((n - 1) + 1), ((∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩ then 1 else 0)) by
      refine Fintype.sum_equiv (finCongr heq_n) _ _ fun r => rfl]
    rw [Fin.sum_univ_castSucc]
    congr 1
    have e1 : (⟨(Fin.last (n - 1)).1, by omega⟩ : Fin (n + 1)) = ⟨n - 1, by omega⟩ := Fin.ext (by simp [Fin.last])
    have e2 : (⟨(Fin.last (n - 1)).1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [Fin.last]; omega)
    simp only [e1, e2]
  dsimp only; exact h2

private lemma step_card_0 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨0 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨0 + i.1, by omega⟩)) nt de := by decide
private lemma step_card_9 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨9 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨9 + i.1, by omega⟩)) nt de := by decide
private lemma step_card_18 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨18 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨18 + i.1, by omega⟩)) nt de := by decide
private lemma step_card_27 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨27 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨27 + i.1, by omega⟩)) nt de := by decide
private lemma step_card_36 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨36 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨36 + i.1, by omega⟩)) nt de := by decide
private lemma step_card_45 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨45 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨45 + i.1, by omega⟩)) nt de := by decide
private lemma step_card_54 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨54 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨54 + i.1, by omega⟩)) nt de := by decide
private lemma step_card_63 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨63 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨63 + i.1, by omega⟩)) nt de := by decide
private lemma step_card_72 : ∀ i : Fin 9, ∀ nt : Fin 14, ∀ de : Fin 2,
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW ⟨72 + i.1, by omega⟩) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW ⟨72 + i.1, by omega⟩)) nt de := by decide

private lemma step_card_code (pc : Fin 81) (nt : Fin 14) (de : Fin 2) :
    (∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW pc) (decW c) = de.1 then 1 else 0) =
    multVal (rowType (decW pc)) nt de := by
  if h0 : pc.1 < 9 then
    have hp : pc = ⟨0 + (pc.1 - 0), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_0 ⟨pc.1 - 0, by omega⟩ nt de
  else
  if h9 : pc.1 < 18 then
    have hp : pc = ⟨9 + (pc.1 - 9), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_9 ⟨pc.1 - 9, by omega⟩ nt de
  else
  if h18 : pc.1 < 27 then
    have hp : pc = ⟨18 + (pc.1 - 18), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_18 ⟨pc.1 - 18, by omega⟩ nt de
  else
  if h27 : pc.1 < 36 then
    have hp : pc = ⟨27 + (pc.1 - 27), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_27 ⟨pc.1 - 27, by omega⟩ nt de
  else
  if h36 : pc.1 < 45 then
    have hp : pc = ⟨36 + (pc.1 - 36), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_36 ⟨pc.1 - 36, by omega⟩ nt de
  else
  if h45 : pc.1 < 54 then
    have hp : pc = ⟨45 + (pc.1 - 45), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_45 ⟨pc.1 - 45, by omega⟩ nt de
  else
  if h54 : pc.1 < 63 then
    have hp : pc = ⟨54 + (pc.1 - 54), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_54 ⟨pc.1 - 54, by omega⟩ nt de
  else
  if h63 : pc.1 < 72 then
    have hp : pc = ⟨63 + (pc.1 - 63), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_63 ⟨pc.1 - 63, by omega⟩ nt de
  else
    have hp : pc = ⟨72 + (pc.1 - 72), by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hp]; exact step_card_72 ⟨pc.1 - 72, by omega⟩ nt de

private lemma step_card (p : Fin 4 → Fin 3) (nt : Fin 14) (de : ℕ) (hde : de ≤ 1) :
    Fintype.card {v : Fin 4 → Fin 3 // rowType v = nt ∧ stepErr p v = de} =
    multVal (rowType p) nt ⟨de, by omega⟩ := by
  let e : {v : Fin 4 → Fin 3 // rowType v = nt ∧ stepErr p v = de} ≃
      {c : Fin 81 // rowType (decW c) = nt ∧ stepErr (decW (encW p)) (decW c) = de} :=
    ⟨fun ⟨v, hv⟩ => ⟨encW v, by rw [decW_encW, decW_encW]; exact hv⟩,
     fun ⟨c, hc⟩ => ⟨decW c, by rw [decW_encW] at hc; exact hc⟩,
     fun ⟨v, _⟩ => Subtype.ext (decW_encW v),
     fun ⟨c, _⟩ => Subtype.ext (encW_decW c)⟩
  rw [Fintype.card_congr e, Fintype.card_subtype]
  have hsum : (Finset.univ.filter (fun c : Fin 81 => rowType (decW c) = nt ∧ stepErr (decW (encW p)) (decW c) = de)).card =
      ∑ c : Fin 81, if rowType (decW c) = nt ∧ stepErr (decW (encW p)) (decW c) = de then 1 else 0 := by
    rw [Finset.card_filter]
  rw [hsum, step_card_code (encW p) nt ⟨de, by omega⟩, decW_encW]

private lemma base1_card_code : ∀ t : Fin 14, ∀ err : Fin 2,
    (∑ code : Fin 81, if rowType (decW code) = t ∧ (0) = err.1 then 1 else 0) =
    base1Val t err.1 := by decide

private lemma card_total_eq_dp (n : ℕ) (hn : 1 ≤ n) :
    ∀ (t : Fin 14) (err : ℕ), err ≤ 1 →
      Fintype.card {A : Fin n → Fin 4 → Fin 3 // mistakes n A = err ∧ rowType (A ⟨n - 1, by omega⟩) = t} =
      dp n t err := by
  induction n with
  | zero => omega
  | succ m ih =>
    cases m with
    | zero =>
      intro t err herr
      let e : {A : Fin 1 → Fin 4 → Fin 3 // mistakes 1 A = err ∧ rowType (A ⟨1 - 1, by omega⟩) = t} ≃
          {code : Fin 81 // rowType (decW code) = t ∧ (0) = err} :=
        ⟨fun x => ⟨encW (x.1 0), by
          rw [decW_encW]; refine ⟨x.2.2, ?_⟩
          have h1 := x.2.1; unfold mistakes at h1; rw [Fin.sum_univ_zero] at h1; exact h1⟩,
         fun x => ⟨fun _ => decW x.1, by
          refine ⟨?_, x.2.1⟩; unfold mistakes; rw [Fin.sum_univ_zero]; exact x.2.2⟩,
         fun x => Subtype.ext (by funext r; fin_cases r; exact decW_encW (x.1 0)),
         fun x => Subtype.ext (encW_decW x.1)⟩
      rw [Fintype.card_congr e, Fintype.card_subtype, Finset.card_filter]
      exact base1_card_code t ⟨err, by omega⟩
    | succ k =>
      intro nt err herr
      let n := k + 1
      have hn' : 1 ≤ n := by omega
      rw [dp_succ_eq n hn' nt err herr]
      let φ : (Σ pt : Fin 14, Σ pe : Fin (err + 1),
          Σ A0 : {A : Fin n → Fin 4 → Fin 3 // mistakes n A = pe.1 ∧ rowType (A ⟨n - 1, by omega⟩) = pt},
          {v : Fin 4 → Fin 3 // rowType v = nt ∧ stepErr (A0.1 ⟨n - 1, by omega⟩) v = err - pe.1}) →
          {A : Fin (n + 1) → Fin 4 → Fin 3 // mistakes (n + 1) A = err ∧ rowType (A ⟨n + 1 - 1, by omega⟩) = nt} :=
        fun ⟨_, pe, ⟨A0, hA0m, _⟩, ⟨v, hv_t, hstep⟩⟩ =>
          ⟨Fin.snoc A0 v, by
            have hcast : (fun r : Fin n => (Fin.snoc A0 v : Fin (n + 1) → Fin 4 → Fin 3) r.castSucc) = A0 := by
              funext r; exact Fin.snoc_castSucc _ _ r
            have hlast : (Fin.snoc A0 v : Fin (n + 1) → Fin 4 → Fin 3) (Fin.last n) = v := Fin.snoc_last _ _
            have hp : (Fin.snoc A0 v : Fin (n + 1) → Fin 4 → Fin 3) ⟨n - 1, by omega⟩ = A0 ⟨n - 1, by omega⟩ := by
              have : (⟨n - 1, by omega⟩ : Fin (n + 1)) = (⟨n - 1, by omega⟩ : Fin n).castSucc := rfl
              rw [this]; exact congrFun hcast ⟨n - 1, by omega⟩
            have hl2 : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [Fin.last])
            constructor
            · rw [mistakes_succ n hn', hcast, hlast, hp, hA0m, hstep]; omega
            · rw [hl2, hlast]; exact hv_t⟩
      have hbij : Function.Bijective φ := by
        constructor
        · rintro ⟨pta, pea, ⟨A0a, hma, hpa⟩, ⟨va, _, _⟩⟩ ⟨ptb, peb, ⟨A0b, hmb, hpb⟩, ⟨vb, _, _⟩⟩ heq
          have hfun : (Fin.snoc A0a va : Fin (n + 1) → Fin 4 → Fin 3) = Fin.snoc A0b vb := congrArg Subtype.val heq
          have hA0 : A0a = A0b := by funext i; simpa using congrFun hfun i.castSucc
          have hv : va = vb := by simpa using congrFun hfun (Fin.last n)
          subst hA0; subst hv
          have hpt : pta = ptb := hpa.symm.trans hpb
          have hpe : pea = peb := Fin.ext (hma.symm.trans hmb)
          subst hpt; subst hpe; rfl
        · rintro ⟨A, hAm, hAt⟩
          let A0 : Fin n → Fin 4 → Fin 3 := fun r => A r.castSucc
          let v : Fin 4 → Fin 3 := A (Fin.last n)
          have hms : mistakes (n + 1) A = mistakes n A0 + stepErr (A0 ⟨n - 1, by omega⟩) v :=
            mistakes_succ n hn' A
          have hpe_lt : mistakes n A0 < err + 1 := by omega
          let pe : Fin (err + 1) := ⟨mistakes n A0, hpe_lt⟩
          let pt : Fin 14 := rowType (A0 ⟨n - 1, by omega⟩)
          have hl2 : (⟨n + 1 - 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp [Fin.last])
          have hvt : rowType v = nt := by rwa [hl2] at hAt
          have hstep : stepErr (A0 ⟨n - 1, by omega⟩) v = err - pe.1 := by dsimp [pe]; omega
          refine ⟨⟨pt, pe, ⟨A0, rfl, rfl⟩, ⟨v, hvt, hstep⟩⟩, ?_⟩
          apply Subtype.ext; funext i; refine Fin.lastCases ?_ ?_ i
          · dsimp [φ, v]; rw [Fin.snoc_last]
          · intro j; dsimp [φ, A0]; rw [Fin.snoc_castSucc]
      rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
      apply Finset.sum_congr rfl; intro pt _
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl; intro pe _
      rw [Fintype.card_sigma]
      let de : Fin 2 := ⟨err - pe.1, by omega⟩
      have hconst : ∀ A0 : {A : Fin n → Fin 4 → Fin 3 // mistakes n A = pe.1 ∧ rowType (A ⟨n - 1, by omega⟩) = pt},
          Fintype.card {v : Fin 4 → Fin 3 // rowType v = nt ∧ stepErr (A0.1 ⟨n - 1, by omega⟩) v = err - pe.1} =
          multVal pt nt de := by
        intro A0; rw [step_card _ nt (err - pe.1) (by omega), A0.2.2]
      have hsum_eq : (∑ A0 : {A : Fin n → Fin 4 → Fin 3 // mistakes n A = pe.1 ∧ rowType (A ⟨n - 1, by omega⟩) = pt},
          Fintype.card {v : Fin 4 → Fin 3 // rowType v = nt ∧ stepErr (A0.1 ⟨n - 1, by omega⟩) v = err - pe.1}) =
          ∑ _A0 : {A : Fin n → Fin 4 → Fin 3 // mistakes n A = pe.1 ∧ rowType (A ⟨n - 1, by omega⟩) = pt},
            multVal pt nt de :=
        Finset.sum_congr rfl fun A0 _ => hconst A0
      rw [hsum_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul, ih hn' pt pe.1 (by omega)]

private lemma uses_ge_2 (n : ℕ) (hn : 1 ≤ n) (A : Fin n → Fin 4 → Fin 3) (hm : mistakes n A = 1) :
    2 ≤ (Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2)).card := by
  by_contra hlt
  have hle1 : (Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2)).card ≤ 1 := by omega
  have hconst : ∀ r1 r2 : Fin n, ∀ c1 c2 : Fin 4, A r1 c1 = A r2 c2 := by
    intro r1 r2 c1 c2
    exact Finset.card_le_one.mp hle1 _ (Finset.mem_image.mpr ⟨(r1, c1), Finset.mem_univ _, rfl⟩)
      _ (Finset.mem_image.mpr ⟨(r2, c2), Finset.mem_univ _, rfl⟩)
  -- For n = 1, mistakes = 0 != 1. For n >= 2, monochromatic array has mistakes >= 6 > 1
  by_cases hn1 : n = 1
  · subst hn1; unfold mistakes at hm; rw [Fin.sum_univ_zero] at hm; omega
  · have hn2 : 2 ≤ n := by omega
    have h1 : 6 ≤ mistakes n A := by
      unfold mistakes
      have h0 : 6 ≤ (∑ c : Fin 3, if A ⟨0, by omega⟩ ⟨c.1, by omega⟩ = A ⟨1, by omega⟩ ⟨c.1 + 1, by omega⟩ then 1 else 0) +
          (∑ c : Fin 3, if A ⟨0, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨1, by omega⟩ ⟨c.1, by omega⟩ then 1 else 0) := by
        have hD : ∀ c : Fin 3, A ⟨0, by omega⟩ ⟨c.1, by omega⟩ = A ⟨1, by omega⟩ ⟨c.1 + 1, by omega⟩ := fun c => hconst _ _ _ _
        have hA : ∀ c : Fin 3, A ⟨0, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨1, by omega⟩ ⟨c.1, by omega⟩ := fun c => hconst _ _ _ _
        simp [hD, hA]
      have hmem : (⟨0, by omega⟩ : Fin (n - 1)) ∈ Finset.univ := Finset.mem_univ _
      have hle := Finset.single_le_sum (f := fun r : Fin (n - 1) => ((∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩ then 1 else 0) + (∑ c : Fin 3, if A ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩ = A ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩ then 1 else 0))) (fun _ _ => Nat.zero_le _) hmem
      dsimp at hle; omega
    omega

private lemma mistakes_comp_perm (n : ℕ) (σ : Equiv.Perm (Fin 3)) (A : Fin n → Fin 4 → Fin 3) :
    mistakes n (fun r c => σ (A r c)) = mistakes n A := by
  unfold mistakes
  simp only [Equiv.apply_eq_iff_eq]

private lemma rowMajor_unique_perm (n : ℕ) (A B : Fin n → Fin 4 → Fin 3)
    (hA : isRowMajor n A) (hB : isRowMajor n B)
    (hcard : 2 ≤ (Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2)).card)
    (σ : Equiv.Perm (Fin 3)) (hσ : (fun r c => σ (A r c)) = B) :
    σ = Equiv.refl _ := by
  have hfix : ∀ v : Fin 3, v ∈ Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2) → σ v = v := by
    intro v hv
    induction hv_val : v.1 using Nat.strong_induction_on generalizing v with
    | _ k ih =>
      have hex : ∃ i : Fin (4 * n), A ⟨i.1 / 4, by omega⟩ ⟨i.1 % 4, by omega⟩ = v := by
        obtain ⟨⟨r, c⟩, _, hrc⟩ := Finset.mem_image.mp hv
        refine ⟨⟨4 * r.1 + c.1, by have := r.2; have := c.2; omega⟩, ?_⟩
        have e1 : (⟨(4 * r.1 + c.1) / 4, by have := r.2; have := c.2; omega⟩ : Fin n) = r := Fin.ext (by dsimp; have := c.2; omega)
        have e2 : (⟨(4 * r.1 + c.1) % 4, by have := r.2; have := c.2; omega⟩ : Fin 4) = c := Fin.ext (by dsimp; have := c.2; omega)
        rw [e1, e2]; exact hrc
      classical
      let i0 := Nat.find (show ∃ idx : ℕ, ∃ h : idx < 4 * n, A ⟨idx / 4, by omega⟩ ⟨idx % 4, by omega⟩ = v by
        obtain ⟨i, hi⟩ := hex; exact ⟨i.1, i.2, hi⟩)
      have hi0_spec := Nat.find_spec (show ∃ idx : ℕ, ∃ h : idx < 4 * n, A ⟨idx / 4, by omega⟩ ⟨idx % 4, by omega⟩ = v by
        obtain ⟨i, hi⟩ := hex; exact ⟨i.1, i.2, hi⟩)
      obtain ⟨hi0_lt, hi0_eq⟩ := hi0_spec
      have hi0_min : ∀ j : Fin (4 * n), j.1 < i0 → A ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩ ≠ v := by
        intro j hj heq; exact Nat.find_min _ hj ⟨j.2, heq⟩
      have hBi0 : B ⟨i0 / 4, by omega⟩ ⟨i0 % 4, by omega⟩ = σ v := by rw [← hσ]; dsimp only; rw [hi0_eq]
      have hge : k ≤ (σ v).1 := by
        by_contra hlt
        have hlt' : (σ v).1 < k := by omega
        obtain ⟨j, hj_lt, hj_eq⟩ := hA ⟨i0, hi0_lt⟩ (σ v).1 (by rw [hi0_eq, hv_val]; exact hlt')
        have hmem_sv : (σ v) ∈ Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2) :=
          Finset.mem_image.mpr ⟨(⟨j.1 / 4, by omega⟩, ⟨j.1 % 4, by omega⟩), Finset.mem_univ _, Fin.ext hj_eq⟩
        have hfix_sv : σ (σ v) = σ v := ih (σ v).1 hlt' (σ v) hmem_sv rfl
        have hveq : σ v = v := σ.injective hfix_sv
        omega
      have hle : (σ v).1 ≤ k := by
        by_contra hgt
        have hlt' : k < (σ v).1 := by omega
        obtain ⟨j, hj_lt, hj_eq⟩ := hB ⟨i0, hi0_lt⟩ k (by rw [hBi0]; exact hlt')
        have hB_j : B ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩ = v := Fin.ext (hj_eq.trans hv_val.symm)
        have hA_j : σ (A ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩) = v := by
          have := congrFun (congrFun hσ ⟨j.1 / 4, by omega⟩) ⟨j.1 % 4, by omega⟩; exact this.trans hB_j
        have hu_ne : A ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩ ≠ v := hi0_min j hj_lt
        have hu_gt : k < (A ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩).1 := by
          by_contra hule
          have hult : (A ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩).1 < k := by
            have : (A ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩).1 ≠ k := fun h => hu_ne (Fin.ext (h.trans hv_val.symm))
            omega
          have hmem_u : A ⟨j.1 / 4, by omega⟩ ⟨j.1 % 4, by omega⟩ ∈ Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2) :=
            Finset.mem_image.mpr ⟨(⟨j.1 / 4, by omega⟩, ⟨j.1 % 4, by omega⟩), Finset.mem_univ _, rfl⟩
          have hfix_u := ih _ hult _ hmem_u rfl
          exact hu_ne (hfix_u.symm.trans hA_j)
        obtain ⟨j', hj'_lt, hj'_eq⟩ := hA j k hu_gt
        exact hi0_min j' (lt_trans hj'_lt hj_lt) (Fin.ext (hj'_eq.trans hv_val.symm))
      exact Fin.ext (by omega)
  ext x
  by_cases hx : x ∈ Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2)
  · exact congrArg Fin.val (hfix x hx)
  · have hnot : σ x ∉ Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2) := by
      intro hmem; exact hx ((σ.injective (hfix (σ x) hmem)) ▸ hmem)
    let S := Finset.univ.image (fun p : Fin n × Fin 4 => A p.1 p.2)
    have hcomp : (Finset.univ \ S).card ≤ 1 := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]; dsimp [S]; omega
    exact congrArg Fin.val (Finset.card_le_one.mp hcomp _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hnot⟩) _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hx⟩))

private lemma exists_perm_rowMajor (n : ℕ) (A : Fin n → Fin 4 → Fin 3) :
    ∃ σ : Equiv.Perm (Fin 3), isRowMajor n (fun r c => σ (A r c)) := by
  classical
  let exP (c : Fin 3) : Prop := ∃ idx : ℕ, ∃ _ : idx < 4 * n, A ⟨idx / 4, by omega⟩ ⟨idx % 4, by omega⟩ = c
  let firstIdx (c : Fin 3) : ℕ := if h : exP c then Nat.find h else 4 * n + c.1
  have hinj : Function.Injective firstIdx := by
    intro a b hab
    dsimp [firstIdx] at hab
    by_cases ha : exP a
    · by_cases hb : exP b
      · rw [dif_pos ha, dif_pos hb] at hab
        have ha_s := Nat.find_spec ha
        have hb_s := Nat.find_spec hb
        have h1 : (⟨Nat.find ha / 4, by have := ha_s.1; omega⟩ : Fin n) = ⟨Nat.find hb / 4, by have := hb_s.1; omega⟩ := Fin.ext (by dsimp; omega)
        have h2 : (⟨Nat.find ha % 4, by have := ha_s.1; omega⟩ : Fin 4) = ⟨Nat.find hb % 4, by have := hb_s.1; omega⟩ := Fin.ext (by dsimp; omega)
        exact ha_s.2.symm.trans (by rw [h1, h2]; exact hb_s.2)
      · rw [dif_pos ha, dif_neg hb] at hab; have := (Nat.find_spec ha).1; omega
    · by_cases hb : exP b
      · rw [dif_neg ha, dif_pos hb] at hab; have := (Nat.find_spec hb).1; omega
      · rw [dif_neg ha, dif_neg hb] at hab; exact Fin.ext (by omega)
  let σ_fn (c : Fin 3) : Fin 3 :=
    ⟨(Finset.univ.filter (fun d : Fin 3 => firstIdx d < firstIdx c)).card, by
      have hlt : (Finset.univ.filter (fun d : Fin 3 => firstIdx d < firstIdx c)) ⊂ Finset.univ := by
        rw [Finset.ssubset_iff_subset_ne]
        refine ⟨Finset.subset_univ _, fun heq => ?_⟩
        have : c ∈ Finset.univ.filter (fun d : Fin 3 => firstIdx d < firstIdx c) := heq.symm ▸ Finset.mem_univ c
        simp at this
      have := Finset.card_lt_card hlt; simpa using this⟩
  have hσ_mono : ∀ a b : Fin 3, firstIdx a < firstIdx b → (σ_fn a).1 < (σ_fn b).1 := by
    intro a b hab; dsimp [σ_fn]; apply Finset.card_lt_card; rw [Finset.ssubset_iff_subset_ne]
    refine ⟨fun d hd => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hd ⊢; omega, fun heq => ?_⟩
    have : a ∈ Finset.univ.filter (fun d : Fin 3 => firstIdx d < firstIdx b) := by simp [hab]
    rw [← heq] at this; simp at this
  have hσ_inj : Function.Injective σ_fn := by
    intro a b hab; by_contra hne
    rcases lt_or_gt_of_ne (fun h => hne (hinj h)) with hlt | hgt
    · exact absurd (congrArg Fin.val hab) (ne_of_lt (hσ_mono a b hlt))
    · exact absurd (congrArg Fin.val hab) (ne_of_gt (hσ_mono b a hgt))
  let σ : Equiv.Perm (Fin 3) := Equiv.ofBijective σ_fn ((Finite.injective_iff_bijective).mp hσ_inj)
  refine ⟨σ, fun i v hv => ?_⟩
  let c := A ⟨i.1 / 4, by omega⟩ ⟨i.1 % 4, by omega⟩
  change v < (σ c).1 at hv
  have hv_lt : v < 3 := lt_trans hv (σ c).2
  let d := σ.symm ⟨v, hv_lt⟩
  have hdv : (σ d).1 = v := by simp [d]
  have hfd_lt : firstIdx d < firstIdx c := by
    by_contra hge
    rcases eq_or_lt_of_le (not_lt.mp hge) with heq | hgt
    · have : d = c := hinj heq.symm; rw [this] at hdv; omega
    · have := hσ_mono c d hgt; change (σ c).1 < (σ d).1 at this; omega
  have hc_ex : exP c := ⟨i.1, i.2, rfl⟩
  have hc_le : firstIdx c ≤ i.1 := by dsimp [firstIdx]; rw [dif_pos hc_ex]; exact Nat.find_min' hc_ex ⟨i.2, rfl⟩
  have hd_lt : firstIdx d < 4 * n := by omega
  have hd_ex : exP d := by
    by_contra hno; dsimp [firstIdx] at hd_lt; rw [dif_neg hno] at hd_lt; omega
  have hd_s := Nat.find_spec hd_ex
  have hd_eq : firstIdx d = Nat.find hd_ex := by dsimp [firstIdx]; rw [dif_pos hd_ex]
  refine ⟨⟨firstIdx d, hd_lt⟩, by dsimp; omega, ?_⟩
  dsimp only
  have h1 : (⟨firstIdx d / 4, by omega⟩ : Fin n) = ⟨Nat.find hd_ex / 4, by have := hd_s.1; omega⟩ := Fin.ext (by dsimp; omega)
  have h2 : (⟨firstIdx d % 4, by omega⟩ : Fin 4) = ⟨Nat.find hd_ex % 4, by have := hd_s.1; omega⟩ := Fin.ext (by dsimp; omega)
  rw [h1, h2, hd_s.2]; exact hdv

private lemma a_eq_total (n : ℕ) (hn : 1 ≤ n) :
    6 * a n = ∑ t : Fin 14, dp n t 1 := by
  unfold a; rw [if_neg (by omega)]
  have htot : Fintype.card {A : Fin n → Fin 4 → Fin 3 // mistakes n A = 1} =
      ∑ t : Fin 14, dp n t 1 := by
    let φ : (Σ t : Fin 14, {A : Fin n → Fin 4 → Fin 3 // mistakes n A = 1 ∧ rowType (A ⟨n - 1, by omega⟩) = t}) →
        {A : Fin n → Fin 4 → Fin 3 // mistakes n A = 1} :=
      fun ⟨_, ⟨A, h, _⟩⟩ => ⟨A, h⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨ta, ⟨Aa, _, hta⟩⟩ ⟨tb, ⟨Ab, _, htb⟩⟩ heq
        have hA : Aa = Ab := congrArg Subtype.val heq; subst hA
        have ht : ta = tb := hta.symm.trans htb; subst ht; rfl
      · rintro ⟨A, hA⟩; exact ⟨⟨rowType (A ⟨n - 1, by omega⟩), ⟨A, hA, rfl⟩⟩, rfl⟩
    rw [Fintype.card_congr (Equiv.ofBijective φ hbij).symm, Fintype.card_sigma]
    apply Finset.sum_congr rfl; intro t _; exact card_total_eq_dp n hn t 1 (le_refl _)
  rw [← htot]
  let ψ : Equiv.Perm (Fin 3) × {A : Fin n → Fin 4 → Fin 3 // mistakes n A = 1 ∧ isRowMajor n A} →
      {A : Fin n → Fin 4 → Fin 3 // mistakes n A = 1} :=
    fun ⟨σ, ⟨A, hAm, _⟩⟩ => ⟨fun r c => σ (A r c), by rw [mistakes_comp_perm]; exact hAm⟩
  have hbij : Function.Bijective ψ := by
    constructor
    · rintro ⟨σa, ⟨Aa, hAma, hAra⟩⟩ ⟨σb, ⟨Ab, _, hArb⟩⟩ heq
      have hfun : (fun r c => σa (Aa r c)) = fun r c => σb (Ab r c) := congrArg Subtype.val heq
      have hcomp : (fun r c => (σb.symm * σa) (Aa r c)) = Ab := by
        funext r c; simp only [Equiv.Perm.mul_apply]; exact congrArg σb.symm (congrFun (congrFun hfun r) c) |>.trans (σb.symm_apply_apply _)
      have hid := rowMajor_unique_perm n Aa Ab hAra hArb (uses_ge_2 n hn Aa hAma) (σb.symm * σa) hcomp
      have hσeq : σa = σb := by
        ext x; have := Equiv.congr_fun hid x
        simp only [Equiv.Perm.mul_apply, Equiv.refl_apply] at this
        exact congrArg Fin.val ((σb.symm_apply_eq).mp this)
      subst hσeq
      have hAeq : Aa = Ab := by funext r c; exact σa.injective (congrFun (congrFun hfun r) c)
      subst hAeq; rfl
    · rintro ⟨A, hAm⟩
      obtain ⟨τ, hτ⟩ := exists_perm_rowMajor n A
      let B : Fin n → Fin 4 → Fin 3 := fun r c => τ (A r c)
      have hBm : mistakes n B = 1 := by rw [mistakes_comp_perm]; exact hAm
      refine ⟨⟨τ.symm, ⟨B, hBm, hτ⟩⟩, ?_⟩
      apply Subtype.ext; funext r c; dsimp [ψ, B]; exact τ.symm_apply_apply _
  rw [← Fintype.card_congr (Equiv.ofBijective ψ hbij), Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
  rfl

private lemma a_closed_m (m : ℕ) : a (m + 3) = (1536 * m + 4032) * 9 ^ m := by
  have htot := a_eq_total (m + 3) (by omega)
  have hdp := dp_closed m
  unfold dpInv at hdp
  obtain ⟨_, h1, _, h3, _, h5, _, h7, _, h9, _, h11, _, h13, _, h15, _, h17, _, h19, _, h21, _, h23, _, h25, _, h27⟩ := hdp
  rw [sum_fin_T] at htot
  rw [h1, h3, h5, h7, h9, h11, h13, h15, h17, h19, h21, h23, h25, h27] at htot
  exact Nat.eq_of_mul_eq_mul_left (by omega : 0 < 6) (by rw [htot]; ring)

private lemma a_zero : a 0 = 0 := by unfold a; simp
private lemma a_val_1 : a 1 = 0 := by
  have h1 := a_eq_total 1 (by omega)
  have hdp : (∑ t : Fin 14, dp 1 t 1) = 0 := by decide
  omega
private lemma a_val_2 : a 2 = 288 := by
  have h1 := a_eq_total 2 (by omega)
  have hdp : (∑ t : Fin 14, dp 2 t 1) = 1728 := by decide
  omega
private lemma a_val_3 : a 3 = 4032 := by
  have h1 := a_eq_total 3 (by omega)
  have hdp : (∑ t : Fin 14, dp 3 t 1) = 24192 := by decide
  omega
private lemma a_val_4 : a 4 = 50112 := by
  have h1 := a_eq_total 4 (by omega)
  have hdp : (∑ t : Fin 14, dp 4 t 1) = 300672 := by decide
  omega

private lemma coeff_X_pow_mul_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ j * f) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  induction j generalizing n with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_assoc]
    cases n with
    | zero => simp
    | succ m =>
      rw [PowerSeries.coeff_succ_X_mul, ih m]
      split_ifs with h1 h2
      · simp [Nat.succ_sub_succ]
      · omega
      · omega
      · rfl

private lemma coeff_mul_X_pow_eq (f : PowerSeries ℚ) (j n : ℕ) :
    PowerSeries.coeff n (f * PowerSeries.X ^ j) = if j ≤ n then PowerSeries.coeff (n - j) f else 0 := by
  rw [mul_comm]; exact coeff_X_pow_mul_eq f j n

theorem solution : type_of% @OMA.S_oeis_a229506.main := by
  have hclosed : ∀ n : ℕ, 2 < n → (a n : ℤ) = 64 * 3 ^ (2 * n - 5) * (8 * (n : ℤ) - 3) := by
    intro n hn
    have h := a_closed_m (n - 3)
    rw [show n - 3 + 3 = n by omega] at h
    have hq : (a n : ℤ) = (1536 * ((n - 3 : ℕ) : ℤ) + 4032) * 9 ^ (n - 3) := by exact_mod_cast h
    have hpow : (3 : ℤ) ^ (2 * n - 5) = 3 * 9 ^ (n - 3) := by
      rw [show 2 * n - 5 = 1 + 2 * (n - 3) by omega, pow_add, pow_mul]; norm_num
    have hn3 : ((n - 3 : ℕ) : ℤ) = (n : ℤ) - 3 := by omega
    rw [hq, hpow, hn3]; ring
  refine ⟨?_, hclosed⟩
  ext n
  have hexp : (1 - 9 * (PowerSeries.X : PowerSeries ℚ)) ^ 2 = 1 - PowerSeries.C 18 * PowerSeries.X ^ 1 + PowerSeries.C 81 * PowerSeries.X ^ 2 := by
    simp only [map_ofNat]; ring
  rw [hexp]
  have hR : (288 * PowerSeries.X ^ 2 * (1 - PowerSeries.X) * (1 - 3 * PowerSeries.X) : PowerSeries ℚ) = PowerSeries.C 288 * PowerSeries.X ^ 2 - PowerSeries.C 1152 * PowerSeries.X ^ 3 + PowerSeries.C 864 * PowerSeries.X ^ 4 := by
    simp only [map_ofNat]; ring
  rw [hR]
  have hc : ∀ (c : ℚ) (j : ℕ), PowerSeries.coeff n (PowerSeries.mk (fun m => (a m : ℚ)) * (PowerSeries.C c * PowerSeries.X ^ j)) =
      c * if j ≤ n then (a (n - j) : ℚ) else 0 := by
    intro c j
    rw [mul_comm (PowerSeries.C c), ← mul_assoc, mul_comm _ (PowerSeries.C c),
        PowerSeries.coeff_C_mul, coeff_mul_X_pow_eq, PowerSeries.coeff_mk]
  simp only [mul_add, mul_sub, mul_one, map_add, map_sub, PowerSeries.coeff_mk, hc,
    PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
  rcases n with _ | _ | _ | _ | _ | m
  · simp [a_zero]
  · simp [a_zero, a_val_1]; try norm_num
  · simp [a_zero, a_val_1, a_val_2]; try norm_num
  · simp [a_val_1, a_val_2, a_val_3]; try norm_num
  · simp [a_val_2, a_val_3, a_val_4]; try norm_num
  · simp only [Nat.add_assoc, Nat.reduceAdd, show 1 ≤ m + 5 by omega, show 2 ≤ m + 5 by omega, ↓reduceIte,
      show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega, show ¬(m + 5 = 2) by omega, show ¬(m + 5 = 3) by omega, show ¬(m + 5 = 4) by omega]
    have ha0 : (a (m + 5) : ℚ) = ((1536 * (m + 2) + 4032) * 9 ^ (m + 2)) := by have h := a_closed_m (m + 2); rw [show m + 2 + 3 = m + 5 by omega] at h; exact_mod_cast h
    have ha1 : (a (m + 4) : ℚ) = ((1536 * (m + 1) + 4032) * 9 ^ (m + 1)) := by have h := a_closed_m (m + 1); rw [show m + 1 + 3 = m + 4 by omega] at h; exact_mod_cast h
    have ha2 : (a (m + 3) : ℚ) = ((1536 * (m + 0) + 4032) * 9 ^ (m + 0)) := by have h := a_closed_m (m + 0); rw [show m + 0 + 3 = m + 3 by omega] at h; exact_mod_cast h
    rw [ha0, ha1, ha2]
    ring

end OMA.P_oeis_a229506

theorem OMA.solution : type_of% @OMA.S_oeis_a229506.main :=
  OMA.P_oeis_a229506.solution
