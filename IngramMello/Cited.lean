import IngramMello.Statements

/-!
# Cited results

The four external inputs of the proof of Theorem 1, each stated in the elementary form
the proof uses. `CitedResults` is their conjunction.

1. `IngramBound`: Proposition 3 of the paper, via Ingram (IMRN 2012), turned into
   integrality and a bound on conjugates after clearing a fixed denominator `D`.
2. `DvornicichZannier`: [DZ07, Theorem L], extending Loxton (1972), for algebraic
   integers of bounded house in `K^cyc`.
3. `Laurent`: Laurent (1984), the torsion case of Lang's conjecture for `𝔾_m^r`, in the
   form of Lemma 2 of the paper.
4. `SuperAttracting`: the dynamical content of Lemma 6 of the paper, for one-parameter
   families over `𝔾_m`. It rests on Branner–Hubbard compactness of the connectedness
   locus and on Dujardin–Favre (2008), Theorem 2.5 and the proof of Proposition 2.4.
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

/-- **Proposition 3** of the paper, in integral form. Source: P. Ingram, *A finiteness result
for post-critically finite polynomials*, Int. Math. Res. Not. IMRN 2012, no. 3, 524–543
(Lemma 2.5 there, together with the computation in the paper). For each `d ≥ 2`
there are an integer `D ≥ 1` and a real `M` with the following property. Let
`f = z^d + a_{d-2} z^{d-2} + ⋯ + a_0` have algebraic coefficients and be PCF. Then each
`D * a_i` is an algebraic integer of house `≤ M`. Also, for every critical point `c` and
all `n, m`, `D * (fⁿ(c) - fᵐ(c))` is an algebraic integer of house `≤ M`. -/
def IngramBound : Prop :=
  ∀ d : ℕ, 2 ≤ d → ∃ D : ℕ, 0 < D ∧ ∃ M : ℝ,
    ∀ a : Fin (d - 1) → ℂ, (∀ i, IsAlgebraic ℚ (a i)) → IsPCF (monicCentred d a) →
      (∀ i, IsBoundedAlgInt M ((D : ℂ) * a i)) ∧
      ∀ c : ℂ, (derivative (monicCentred d a)).IsRoot c → ∀ n m : ℕ,
        IsBoundedAlgInt M ((D : ℂ) *
          ((fun z => (monicCentred d a).eval z)^[n] c -
            (fun z => (monicCentred d a).eval z)^[m] c))

/-! ### 2. Dvornicich–Zannier, Theorem L -/

/-- **Dvornicich–Zannier, Theorem L**, bounded-house form. Source: R. Dvornicich and
U. Zannier, *Cyclotomic diophantine problems (Hilbert irreducibility and invariant sets for
polynomial maps)*, Duke Math. J. 139 (2007), no. 3, 527–554, Theorem L; it extends
J. H. Loxton, *On the maximum modulus of cyclotomic integers*, Acta Arith. 22 (1972), 69–85.

Fix a number field `K ⊆ ℂ` and a bound
`B`. There are a finite set `E ⊆ K` and an integer `N` such that every algebraic integer
`α ∈ K^cyc` with house `≤ B` can be written `α = ∑_{i<n} c_i ξ_i` with `n ≤ N`, each
`c_i ∈ E`, and each `ξ_i` a root of unity. Repetitions are allowed. -/
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

/-- **Laurent's theorem**, in the form of Lemma 2 of the paper. Source: M. Laurent, *Équations
diophantiennes exponentielles*, Invent. Math. 78 (1984), no. 2, 299–327. Let `T` be
an infinite set of torsion points of `(ℂ^×)^r`. Then some positive-dimensional torsion
coset `C = η H` meets `T` in a Zariski-dense subset of `C`.

Here `C` is `{cosetPt η B w : w ∈ (ℂ^×)^s}` with `s ≥ 1`, each `η_j` a root of unity, and
`B` of rank `s` (`B.mulVec` injective on `ℤ^s`, so `w ↦ w^B` has finite kernel). Zariski
density means: a Laurent polynomial vanishing on `T ∩ C` vanishes on all of `C`. -/
def Laurent : Prop :=
  ∀ (r : ℕ) (T : Set (Fin r → ℂ)), (∀ t ∈ T, ∀ j, IsRootOfUnityC (t j)) → T.Infinite →
    ∃ (s : ℕ) (η : Fin r → ℂ) (B : Matrix (Fin r) (Fin s) ℤ),
      0 < s ∧ (∀ j, IsRootOfUnityC (η j)) ∧ Function.Injective B.mulVec ∧
      ∀ P : MvLaurent r,
        (∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → cosetPt η B w ∈ T →
          MvLaurent.eval P (cosetPt η B w) = 0) →
        ∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → MvLaurent.eval P (cosetPt η B w) = 0

/-! ### 4. Super-attracting parameters (dynamical content of Lemma 6) -/

/-- An algebraic closure of `ℂ(t)`, the function field of `𝔾_m`. Generic critical points
of a family over `ℂ[t, t⁻¹]` live here. -/
abbrev GenericField := AlgebraicClosure (FractionRing (LaurentPolynomial ℂ))

/-- **Super-attracting parameters** (Lemma 6 of the paper for `r = 1`). Sources: R. Dujardin
and C. Favre, *Distribution of rational maps with a preperiodic critical point*, Amer. J. Math.
130 (2008), no. 4, 979–1032, Theorem 2.5 and Proposition 2.4 with its proof; and B. Branner
and J. H. Hubbard, *The iteration of cubic polynomials. Part I: The global topology of
parameter space*, Acta Math. 160 (1988), 143–206, for the compactness of the connectedness
locus. Let
`f_t(z) = z^d + a_{d-2}(t) z^{d-2} + ⋯ + a_0(t)` with `a_i ∈ ℂ[t, t⁻¹]`, not all constant
(for monic centred families this is non-isotriviality). Then there is a monic
`P ∈ ℂ[t, t⁻¹][z]` whose roots in `\overline{ℂ(t)}` are all critical points of `f` with
infinite forward orbit. Moreover some `t₀ ∈ ℂ^×` and some root `c₀` of the specialization
`P_{t₀}` satisfy `f_{t₀}^q(c₀) = c₀` for some `q ≥ 1`.

In the language of Dujardin–Favre: some critical point with infinite generic orbit becomes periodic
at `t₀` on the normalization of `𝔾_m` in a splitting field of `f'`. Its minimal
polynomial over `ℂ(t)` has coefficients in `ℂ[t, t⁻¹]` and can serve as `P`. -/
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

/-- The cited results, bundled. -/
def CitedResults : Prop :=
  IngramBound ∧ DvornicichZannier ∧ Laurent ∧ SuperAttracting

end IngramMello
