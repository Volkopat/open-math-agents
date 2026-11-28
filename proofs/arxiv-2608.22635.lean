import OMAStatements.S_arxiv_2608_22635
import Mathlib

theorem OMA.disproof : ¬ (type_of% @OMA.S_arxiv_2608_22635.main) := by
  intro h
  have hspec :=
    h 5 115 19726599787079129775103071759543738099950374011720
      24 9931414749943516928215699 47629391928872028421837349
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)
      34307130064485443087135776973119544521652824368
      676763024625374553353727805340922262877605894543645958977994892519160014502019539531684733592961
      (by norm_num)
  norm_num at hspec
