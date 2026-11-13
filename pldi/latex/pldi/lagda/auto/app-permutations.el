;; -*- lexical-binding: t; -*-

(TeX-add-style-hook
 "app-permutations"
 (lambda ()
   (LaTeX-add-labels
    "sec:form"
    "app:sn-gates"
    "app:sn-relations"
    "app:sn-cosets"
    "fig:sn-pushing"))
 :latex)

