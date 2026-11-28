import OMAReductions.R_OeisA135508_conjecture_R1

theorem OMA.solution : OMA.R_OeisA135508_conjecture_R1.H1 :=
  Nat.le_induction (by decide) (fun n hn h =>
    h.trans (OMA.R_OeisA135508_conjecture_R1.x_dvd_succ n (by omega)))
