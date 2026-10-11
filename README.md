# Postcritically finite polynomials over cyclotomic closures: Lean formalization

A Lean 4 / Mathlib formalization accompanying P. Ingram and J. Mello, *Postcritically finite polynomials over cyclotomic closures of number fields*.

`IngramMello/Paper.lean` states the numbered results of the paper that are formalized, in the paper's numbering. Theorem 1 is `IngramMello.theorem1 : MainStatement`, with `MainStatement` defined in `IngramMello/Statements.lean`. It depends on no unproved external results. The published inputs to the paper's proof (a consequence of Ingram's bounds for PCF polynomials, a bounded-house consequence of Theorem L of Dvornicich and Zannier together with a qualitative form of Loxton's theorem, Lemma 2 from Laurent's theorem, and the one-parameter case of Lemma 6) are proved in this repository, in the forms stated in `IngramMello/Inputs.lean`.

To check:

    lake exe cache get
    lake build
    lake env lean CheckAxioms.lean

The last command should report that each theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

This formalization was produced with the assistance of AI tools.
