# Postcritically finite polynomials over cyclotomic closures: Lean formalization

A Lean 4 / Mathlib formalization accompanying P. Ingram and J. Mello, *Postcritically finite polynomials over cyclotomic closures of number fields*.

`IngramMello/Paper.lean` exports the numbered results and documents their Lean forms. Theorem 1 is `IngramMello.theorem1 : MainStatement`, with `MainStatement` defined in `IngramMello/Statements.lean`. The four published inputs are bundled as `Inputs` in `IngramMello/Inputs.lean` and proved by `IngramMello.inputs`. No mathematical results are assumed beyond Lean's standard axioms.

To check:

    lake exe cache get
    lake build
    lake env lean CheckAxioms.lean

The last command should report that each theorem depends only on `propext`, `Classical.choice` and `Quot.sound`.

This formalization was produced with the assistance of AI tools.
