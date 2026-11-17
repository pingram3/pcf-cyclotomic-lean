import IngramMello.Theorem1
import IngramMello.Exceptional
import IngramMello.IngramBound
import IngramMello.SuperAttractingProof
import IngramMello.LaurentProof
import IngramMello.DvornicichZannier

/-!
# The numbered results of the paper

This file exports the numbered results in their formalized forms. All inputs are proved in
this repository; no mathematical results are assumed beyond Lean's standard axioms.

* **Theorem 1**: `theorem1`: as stated.
* **Lemma 2**: `lemma2`: over `ℂ`, with a monomial parametrization of the torsion coset.
* **Proposition 3**: `proposition3`: integral bounds on coefficients and iterate differences.
* **Lemma 4**: `lemma4`: algebraic integers of bounded house replace the adelic hypothesis.
* **Lemma 5**: `lemma5`: as stated.
* **Lemma 6**: `lemma6`: a monic polynomial and a periodic specialization encode the parameter.
* **Lemma 7**: `lemma7`: the critical points with infinite orbit are specified as a set.
* **Lemma 9**: `lemma9`: as stated.

Lemma 8 is not formalized: a pigeonhole argument on vanishing-coordinate patterns in
`mainStatement_of_not_isExceptional` takes its place and produces an exceptional family.

The four published inputs are Ingram's bound (`proposition3`), the bounded-house consequence
of Dvornicich–Zannier's Theorem L (`dvornicichZannier_theoremL`, via Loxton and Cassels),
Laurent's torsion result (`lemma2`, via Mann), and the one-parameter super-attracting result
(`superAttracting_oneParameter`, attributed in the paper to Dujardin–Favre and Branner–Hubbard).
Their statements are bundled as `Inputs`; `inputs` proves the conjunction.
-/

namespace IngramMello

open Polynomial

/-- The conjunction of the four statements in `Inputs.lean`. -/
theorem inputs : Inputs :=
  ⟨ingramBound_of_local, dvornicichZannier_of_loxton, laurent_of_mann,
    superAttracting_of_algebraic⟩

/-- **Theorem 1.** Let `K` be a number field and `d ≥ 2`. There are only finitely many monic
centred PCF polynomials of degree `d` with coefficients in `K^cyc`.

Lean form: `MainStatement` of `Statements.lean`. -/
theorem theorem1 : MainStatement :=
  mainStatement_of_not_isExceptional ingramBound_of_local dvornicichZannier_of_loxton
    fun d hd K hK r a T => not_isExceptional ingramBound_of_local dvornicichZannier_of_loxton
      laurent_of_mann superAttracting_of_algebraic d hd K hK r a T

/-- **Lemma 2** (Laurent). Paper statement: if `T ⊆ 𝔾_m^r` is an infinite set of torsion points,
then there is a positive-dimensional torsion coset `η H ⊆ 𝔾_m^r` such that `η H ∩ T` is Zariski
dense in `η H`.

Lean form: the statement `Laurent` of `Inputs.lean`, which is the statement of Lemma 2 over the
complex numbers and not the full finite-union form of Laurent's theorem (that the Zariski
closure of any set of torsion points is a finite union of torsion cosets). The coset is
`{η · w^B : w ∈ (ℂ^×)^s}` with `s ≥ 1`, `η` torsion and `B ∈ ℤ^{r × s}` of rank `s`
(`B.mulVec` injective on `ℤ^s`). The monomial map `w ↦ η · w^B` has finite kernel (it is a
finite cover of the coset, not necessarily an isomorphism onto it). Zariski density says that
a Laurent polynomial vanishing at the points of `T` on the coset vanishes on the whole coset. See
`LaurentProof.lean` for the proof and reference. -/
theorem lemma2 : Laurent := laurent_of_mann

/-- **Proposition 3** (adelic bounds). Paper statement: there is an adelic constant
`M_v = M(d, v) ≥ 1` such that for every monic centred PCF polynomial
`f = z^d + a_{d-2} z^{d-2} + ⋯ + a_0 ∈ \overline{ℚ}[z]`, every place `v` and every extension of
`|·|_v` to `\overline{ℚ}`: (i) `|a_i|_v ≤ M_v`; (ii) for every critical point `c` and all
`n, m ≥ 0`, `|fⁿ(c)|_v ≤ M_v` and `|fⁿ(c) - fᵐ(c)|_v ≤ M_v`.

Lean form: the integral bounded-house statement `IngramBound` of `Inputs.lean`. For each `d`
there are `D ≥ 1` and `M` such that `D a_i` and `D (fⁿ(c) - fᵐ(c))` are algebraic integers of
house at most `M`; this is the adelic bound with the finitely many places where `M_v > 1` cleared
by `D`, which depends only on `d`. The bound on `|fⁿ(c)|_v` alone is not stated; Theorem 1
uses only coefficients and iterate differences. The proof in `IngramBound.lean` uses
`IngramForms.lean`, `Escape.lean` and `EscapeArch.lean`; the reference is in `IngramForms.lean`. -/
theorem proposition3 : IngramBound := ingramBound_of_local

/-- **Lemma 4** (fixed linear form). Paper statement: let `K` be a number field and `M_v` an
adelic constant. Then there is a linear form `L(x) = e_1 x_1 + ⋯ + e_m x_m ∈ K[x]` such that
every `α ∈ K^cyc` with `|α|_w ≤ M_v` for all places can be written as `α = L(ζ_1, …, ζ_m)` with
each `ζ_i` zero or a root of unity.

Lean form: the adelic hypothesis on `α` is replaced by "`α` is an algebraic integer with house
at most `B`" (the paper's proof reduces to this case by clearing a denominator `D`, and the
formalized Proposition 3, `IngramBound`, is stated directly in this integral form). The input is
the bounded-house consequence of Theorem L; see `dvornicichZannier_theoremL` for its scope. -/
theorem lemma4 (K : IntermediateField ℚ ℂ) (hK : FiniteDimensional ℚ K) (B : ℝ) :
    ∃ (m : ℕ) (e : Fin m → ℂ), (∀ i, e i ∈ K) ∧
      ∀ α ∈ Kcyc K, IsIntegral ℤ α → HouseLE α B →
        ∃ y : Fin m → ℂ, (∀ i, y i = 0 ∨ IsRootOfUnityC (y i)) ∧ α = ∑ i, e i * y i :=
  exists_linearForm dvornicichZannier_of_loxton K hK B

/-- **Lemma 5** (Hajós). Paper statement: let `x ∈ 𝔾_m^r(ℂ)` and let `F` be a nonzero Laurent
polynomial in `r` variables expressible as a linear combination of at most `T` monomials. Then
`ord_x F ≤ T - 1`.

Lean form: `F ∈ ℂ[u_1^{±1}, …, u_r^{±1}]` has at most `T` monomials when its support has at
most `T` elements, and `ord_x F ≤ T - 1` is expressed as `F ∉ 𝔪_x ^ T`, where `𝔪_x` is the
maximal ideal of `x` in the Laurent polynomial ring. -/
theorem lemma5 {r : ℕ} (x : Fin r → ℂˣ) (T : ℕ) (F : MvLaurent r) (hF : F ≠ 0)
    (hT : F.coeff.support.card ≤ T) : F ∉ MvLaurent.maxIdeal x ^ T :=
  MvLaurent.hajos x T F hF hT

/-- **Lemma 6** (super-attracting parameters). Paper statement: let `R = ℂ[𝔾_m^r]` and let
`f ∈ R[z]` be monic, centred and non-isotrivial. Then there is a super-attracting parameter
`x ∈ 𝔾_m^r(ℂ)` for `f`, i.e. a critical point `c` of `f` with infinite forward orbit, defined
over a finite extension of `Frac R`, which becomes periodic at a point above `x`.

Lean form: `f = monicCentred d a` with `a_i ∈ ℂ[u_1^{±1}, …, u_r^{±1}]` not all constant. The
super-attracting parameter is given by a monic `P ∈ R[z]` whose roots in the algebraic closure
of `Frac R` are critical points of `f` with infinite forward orbit, a point `x ∈ (ℂ^×)^r`, and a
root `c₀` of the specialization `P_x` with `f_x^q(c₀) = c₀` for some `q ≥ 1`. The case `r = 1`
is `SuperAttracting` of `Inputs.lean`; see `superAttracting_oneParameter`. The general case is
reduced to it along a generic monomial curve, as in the paper. -/
theorem lemma6 {r d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → MvLaurent r)
    (hnc : ∃ i, MvLaurent.NonConst (a i)) :
    ∃ P : (MvLaurent r)[X], P.Monic ∧
      (∀ c : AlgebraicClosure (FractionRing (MvLaurent r)), aeval c P = 0 →
        aeval c (derivative (monicCentred d a)) = 0 ∧ ¬ HasFiniteOrbit (monicCentred d a) c) ∧
      ∃ (x : Fin r → ℂˣ) (c₀ : ℂ) (q : ℕ), 0 < q ∧
        (P.map (MvLaurent.evalHom x : MvLaurent r →+* ℂ)).IsRoot c₀ ∧
        (fun z => ((monicCentred d a).map
          (MvLaurent.evalHom x : MvLaurent r →+* ℂ)).eval z)^[q] c₀ = c₀ := by
  have : IsIntegrallyClosed (MvLaurent r) := isIntegrallyClosed_mvLaurent ℂ r
  obtain ⟨A, B, n, m, N, hAm, -, hfg, hnm, hBN, hiff⟩ :=
    exists_infiniteOrbitFactor_monicCentred hd a
  refine ⟨A, hAm, fun c hc => (hiff c).1 hc, ?_⟩
  obtain ⟨x, c₀, q, hq, hroot, -, hper⟩ :=
    exists_superAttracting_root superAttracting_of_algebraic (RingHom.id _) hd a hnc hnm rfl
      hBN hfg
  rw [RingHom.comp_id] at hroot hper
  exact ⟨x, c₀, q, hq, hroot, hper⟩

/-- **Lemma 7** (high-order resultants). Paper statement: let `R = ℂ[u_1^{±1}, …, u_r^{±1}]`,
let `f = z^d + a_{d-2} z^{d-2} + ⋯ + a_0 ∈ R[z]`, let `S` be the multiset of critical points of
`f` with infinite forward orbit, and `W_{ℓ,k} = ∏_{c ∈ S} (f^ℓ(c) - f^k(c))`. Then `W_{ℓ,k} ∈ R`,
`W_{ℓ,k} ≠ 0` for `ℓ ≠ k`, `W_{ℓ,k}` has coefficients in `k₀` if the `a_i` do, and if `x` is a
super-attracting parameter then there is `q` with `ord_x W_{q(ℓ+1),qℓ} ≥ ℓ + 1` for all `ℓ`.

Lean form: the coefficients live in an integrally closed `ℚ`-algebra domain `R₀` mapping to
`ℂ[u^{±1}]` by `ι` (in the paper `R₀ = k₀[u^{±1}]`, and `R₀ = R` when `k₀ = ℂ`). The exported
statement asserts the existence of a monic `A ∈ R₀[z]` such that `A` divides `f'` and such that
a point `c` of the algebraic closure of `Frac R₀` is a root of `A` if and only if `c` is a
critical point of `f` with infinite forward orbit; that is, the roots of `A` are exactly the
critical points with infinite orbit as a set. Nothing is asserted about the multiplicities of
the roots of `A`, so `A` need not be the product over the paper's multiset `S`. The paper's
`W_{ℓ,k}` is replaced by `W A f ℓ k = Res(A, f^ℓ - f^k)`, an element of `R₀`, which is asserted
to be nonzero for `ℓ ≠ k`. A super-attracting parameter is given as `x ∈ (ℂ^×)^r`, `q ≥ 1` and
a root `c₀` of `A_x` with `f_x^q(c₀) = c₀`; the order bound
`ord_x W A f (q(ℓ+1)) (qℓ) ≥ ℓ + 1` then holds for this `q` and all `ℓ`. -/
theorem lemma7 {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀] [Algebra ℚ R₀]
    {r : ℕ} (ι : R₀ →+* MvLaurent r) {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R₀) :
    ∃ A : R₀[X], A.Monic ∧ A ∣ derivative (monicCentred d a) ∧
      (∀ c : AlgebraicClosure (FractionRing R₀), aeval c A = 0 ↔
        (aeval c (derivative (monicCentred d a)) = 0 ∧
          ¬ HasFiniteOrbit (monicCentred d a) c)) ∧
      (∀ l j, l ≠ j → W A (monicCentred d a) l j ≠ 0) ∧
      ∀ (x : Fin r → ℂˣ) (c₀ : ℂ) (q : ℕ), 0 < q →
        (A.map ((MvLaurent.evalHom x : MvLaurent r →+* ℂ).comp ι)).IsRoot c₀ →
        (fun z => ((monicCentred d a).map
          ((MvLaurent.evalHom x : MvLaurent r →+* ℂ).comp ι)).eval z)^[q] c₀ = c₀ →
        ∀ l, ι (W A (monicCentred d a) (q * (l + 1)) (q * l)) ∈
          MvLaurent.maxIdeal x ^ (l + 1) := by
  obtain ⟨A, B, n, m, N, hAm, -, hfg, hnm, hBN, hiff⟩ :=
    exists_infiniteOrbitFactor_monicCentred hd a
  set f := monicCentred d a
  refine ⟨A, hAm, ⟨C (d : R₀) * B, by rw [hfg]; ring⟩, hiff, fun l j hlj => ?_,
    fun x c₀ q hq hA₀ hper l => ?_⟩
  · refine W_ne_zero hAm f ((algebraMap (FractionRing R₀) (AlgebraicClosure (FractionRing R₀))).comp
      (algebraMap R₀ (FractionRing R₀))) l j fun c hc heq => ?_
    have h := (hiff c).1 (by rw [aeval_eq_eval_map_algebraicClosure]; exact hc)
    exact h.2 ((hasFiniteOrbit_iff_algebraicClosure f c).2 (finite_orbit_of_iterate_eq _ hlj heq))
  · refine map_W_mem_maxIdeal_pow hAm f ι x hq hA₀ ?_ hper l
    rw [derivative_map, hfg, Polynomial.map_mul, Polynomial.map_mul, eval_mul, eval_mul,
      hA₀.eq_zero, zero_mul, mul_zero]

/-- **Lemma 9.** There are no exceptional families: for every `d ≥ 2`, every number field `K`,
every `r`, every tuple of Laurent polynomials `a_{d-2}, …, a_0 ∈ K[u_1^{±1}, …, u_r^{±1}]` and
every set `T` of torsion points of `(ℂ^×)^r`, `(a, T)` is not an exceptional family
(`IsExceptional` of `Descent.lean`). The paper's finite extension `K'/K` is absorbed into `K`,
which ranges over all number fields. -/
theorem lemma9 (d : ℕ) (hd : 2 ≤ d) (K : IntermediateField ℚ ℂ) (hK : FiniteDimensional ℚ K)
    (r : ℕ) (a : Fin (d - 1) → AddMonoidAlgebra K (Fin r → ℤ)) (T : Set (Fin r → ℂˣ)) :
    ¬ IsExceptional d K r a T :=
  not_isExceptional ingramBound_of_local dvornicichZannier_of_loxton laurent_of_mann
    superAttracting_of_algebraic d hd K hK r a T

/-! ### Published results used as inputs, proved here -/

/-- **The bounded-house consequence of Dvornicich–Zannier's Theorem L** used in the proof of
Lemma 4, in the form `DvornicichZannier` of `Inputs.lean`: for a number field `K ⊆ ℂ` and a
house bound `B` there are a finite set `E ⊆ K` and an integer `N` such that every algebraic
integer `α ∈ K^cyc` of house at most `B` is a sum of at most `N` terms `c ξ` with `c ∈ E` and
`ξ` a root of unity; repetitions are allowed.

Source: R. Dvornicich and U. Zannier, *Cyclotomic diophantine problems (Hilbert irreducibility
and invariant sets for polynomial maps)*, Duke Math. J. 139 (2007), no. 3, 527–554, Theorem L,
which extends Loxton's theorem. The proof is `dvornicichZannier_of_loxton` in
`DvornicichZannier.lean`.

This is not Theorem L itself. In Theorem L the finite set `E` depends only on `K`, its
cardinality is bounded, and the number of terms is bounded effectively in terms of Loxton's
function of the house. Here `E` may depend on the house bound `B`, no bound on the cardinality
of `E` is asserted, and no effective (Loxton-function) bound on the number of terms `N` is
asserted: only the existence of `E` and `N` is proved. -/
theorem dvornicichZannier_theoremL : DvornicichZannier := dvornicichZannier_of_loxton

/-- **Loxton's theorem**, qualitative bounded-house form: for every house bound `B` there is
`Λ` such that every algebraic integer of house at most `B` in a cyclotomic field `ℚ(ζ_n)` is a
sum of at most `Λ` roots of unity (`SumRoots Λ` of `CasselsHeight.lean`). Only the existence of
`Λ` is asserted; Loxton's explicit (effective) dependence of `Λ` on `B` is not formalized.
See `Loxton.lean` for the proof and reference, and `CasselsHeight.lean` for Cassels' height. -/
theorem loxton_theorem (B : ℝ) :
    ∃ Λ : ℕ, ∀ n, 0 < n → ∀ β ∈ cycField n, IsIntegral ℤ β → HouseLE β B → β ∈ SumRoots Λ :=
  loxton_house B

/-- **Super-attracting parameters for one-parameter families** (Lemma 6 for `r = 1`),
the statement `SuperAttracting` of `Inputs.lean`. The paper deduces this from R. Dujardin and
C. Favre, *Distribution of rational maps with a preperiodic critical point*, Amer. J. Math.
130 (2008), no. 4, 979–1032, Theorem 2.5 and Proposition 2.4 with its proof, and B. Branner and
J. H. Hubbard, *The iteration of cubic polynomials. Part I: The global topology of parameter
space*, Acta Math. 160 (1988), 143–206, for compactness of the connectedness locus.

For monic centred families, nonconstant coefficients express non-isotriviality. In the
language of Dujardin–Favre, a critical point with infinite generic orbit becomes periodic at
`t₀` on the normalization of `𝔾_m` in a splitting field of `f'`. Its minimal polynomial over
`ℂ(t)` has coefficients in `ℂ[t, t⁻¹]` and can serve as `P` in `lemma6`.
See `SuperAttractingProof.lean` for the algebraic proof using two places of a finite extension
of `ℂ(t)` in place of complex dynamics. -/
theorem superAttracting_oneParameter : SuperAttracting := superAttracting_of_algebraic

end IngramMello
