import IngramMello.Statements

/-!
# The four inputs to the proof of Theorem 1

The propositions below state the published inputs in the forms used by the proof:
`IngramBound` (Proposition 3), `DvornicichZannier` (the bounded-house consequence of Theorem L),
`Laurent` (Lemma 2), and `SuperAttracting` (Lemma 6 for one parameter).

`Inputs` is their conjunction. The deduction of Theorem 1 takes these statements as
hypotheses; `inputs` in `Paper.lean` discharges them. The theorem docstrings there explain the
comparison with the paper and point to the proofs and bibliographic references.
-/

namespace IngramMello

open Polynomial

/-! ### Houses and bounded algebraic integers -/

/-- Every complex conjugate of `x` (every complex root of its minimal polynomial over
`ℚ`) has modulus at most `M`, i.e. the house of `x` is at most `M`. If `x` is
transcendental then `minpoly ℚ x = 0` and this fails for every `M`. -/
def HouseLE (x : ℂ) (M : ℝ) : Prop :=
  ∀ z : ℂ, aeval z (minpoly ℚ x) = 0 → ‖z‖ ≤ M

/-- `x` is an algebraic integer whose house is at most `M`. -/
def IsBoundedAlgInt (M : ℝ) (x : ℂ) : Prop :=
  IsIntegral ℤ x ∧ HouseLE x M

/-! ### 1. Ingram's adelic bound -/

/-- **Proposition 3**, in integral bounded-house form: one denominator `D` and bound `M`
work for all coefficients and differences of critical iterates in degree `d`.
See `proposition3` in `Paper.lean` for the comparison with the adelic statement. -/
def IngramBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ D : ℕ, 0 < D ∧ ∃ M : ℝ,
    ∀ a : Fin (d - 1) → ℂ, (∀ i, IsAlgebraic ℚ (a i)) → IsPCF (monicCentred d a) →
      (∀ i, IsBoundedAlgInt M ((D : ℂ) * a i)) ∧
      ∀ c : ℂ, (derivative (monicCentred d a)).IsRoot c → ∀ n m : ℕ,
        IsBoundedAlgInt M ((D : ℂ) *
          ((fun z => (monicCentred d a).eval z)^[n] c -
            (fun z => (monicCentred d a).eval z)^[m] c))

/-! ### 2. The bounded-house consequence of Dvornicich–Zannier's Theorem L -/

/-- The bounded-house consequence of **Dvornicich–Zannier's Theorem L** used in Lemma 4.
See `dvornicichZannier_theoremL` in `Paper.lean` for the statement's scope and reference. -/
def DvornicichZannier : Prop :=
  ∀ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K → ∀ B : ℝ,
    ∃ E : Finset ℂ, (∀ e ∈ E, e ∈ K) ∧ ∃ N : ℕ,
      ∀ α ∈ Kcyc K, IsIntegral ℤ α → HouseLE α B →
        ∃ (n : ℕ) (c ξ : Fin n → ℂ), n ≤ N ∧ (∀ i, c i ∈ E) ∧
          (∀ i, IsRootOfUnityC (ξ i)) ∧ α = ∑ i, c i * ξ i

/-! ### 3. Laurent's theorem on torsion points of tori -/

/-- Laurent polynomials in `r` variables over `ℂ`: finitely supported functions
`ℤ^r → ℂ`, where `e ↦ β` stands for the monomial `β u^e`. -/
abbrev MvLaurent (r : ℕ) := AddMonoidAlgebra ℂ (Fin r → ℤ)

/-- Evaluate a Laurent polynomial at `u ∈ ℂ^r`. This is meaningful when every `u j ≠ 0`. -/
noncomputable def MvLaurent.eval {r : ℕ} (P : MvLaurent r) (u : Fin r → ℂ) : ℂ :=
  P.coeff.sum fun e β => β * ∏ j, u j ^ e j

/-- The point `η · w^B` with `j`-th coordinate `η_j ∏_k w_k^{B j k}`. As `w` ranges over
`(ℂ^×)^s`, these points make up a coset `η H` of the subtorus `H = image of w ↦ w^B`.
When `B` has rank `s`, `H` has dimension `s`. Every coset of an `s`-dimensional subtorus
arises this way. -/
noncomputable def cosetPt {r s : ℕ} (η : Fin r → ℂ) (B : Matrix (Fin r) (Fin s) ℤ)
    (w : Fin s → ℂ) : Fin r → ℂ :=
  fun j => η j * ∏ k, w k ^ B j k

/-- **Lemma 2**, over `ℂ`: an infinite torsion set meets a positive-dimensional torsion
coset in a Zariski-dense set. See `lemma2` in `Paper.lean` for the parametrization and scope. -/
def Laurent : Prop :=
  ∀ (r : ℕ) (T : Set (Fin r → ℂ)), (∀ t ∈ T, ∀ j, IsRootOfUnityC (t j)) → T.Infinite →
    ∃ (s : ℕ) (η : Fin r → ℂ) (B : Matrix (Fin r) (Fin s) ℤ),
      0 < s ∧ (∀ j, IsRootOfUnityC (η j)) ∧ Function.Injective B.mulVec ∧
      ∀ P : MvLaurent r,
        (∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → cosetPt η B w ∈ T →
          MvLaurent.eval P (cosetPt η B w) = 0) →
        ∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → MvLaurent.eval P (cosetPt η B w) = 0

/-! ### 4. Super-attracting parameters (Lemma 6 in the one-parameter case) -/

/-- An algebraic closure of `ℂ(t)`, the function field of `𝔾_m`. Generic critical points
of a family over `ℂ[t, t⁻¹]` live here. -/
abbrev GenericField := AlgebraicClosure (FractionRing (LaurentPolynomial ℂ))

/-- **Lemma 6 for one parameter.** A nonconstant monic centred family over `ℂ[t, t⁻¹]`
has a monic polynomial whose roots are critical points with infinite generic orbit,
and a periodic specialization.
See `lemma6` and `superAttracting_oneParameter` in `Paper.lean` for details and references. -/
def SuperAttracting : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∀ a : Fin (d - 1) → LaurentPolynomial ℂ,
    (∃ i, a i ∉ Set.range (LaurentPolynomial.C : ℂ →+* LaurentPolynomial ℂ)) →
    ∃ P : (LaurentPolynomial ℂ)[X], P.Monic ∧
      (∀ c : GenericField, aeval c P = 0 →
        aeval c (derivative (monicCentred d a)) = 0 ∧
          ¬ HasFiniteOrbit (monicCentred d a) c) ∧
      ∃ (t₀ : ℂˣ) (c₀ : ℂ) (q : ℕ), 0 < q ∧
        (P.map (LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀)).IsRoot c₀ ∧
        (fun z => ((monicCentred d a).map
          (LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀)).eval z)^[q] c₀ = c₀

/-- The four inputs, bundled. -/
def Inputs : Prop :=
  IngramBound ∧ DvornicichZannier ∧ Laurent ∧ SuperAttracting

end IngramMello
