import IngramMello.Theorem1
import IngramMello.Exceptional

/-!
# The numbered results of the paper

This file states each numbered result of the paper in the form in which it is formalized,
proved from the development in the other files. The cited inputs are the four propositions
of `Cited.lean`, bundled as `CitedResults`.

Status of the numbered results:

* **Theorem 1** (finiteness of monic centred PCF polynomials over `K^cyc`): proved as
  stated, assuming `CitedResults`. Lean: `theorem1`.
* **Lemma 2** (Laurent's theorem on torsion points of tori): cited. Source: M. Laurent,
  *Équations diophantiennes exponentielles*, Invent. Math. 78 (1984), no. 2, 299–327.
  Lean: the proposition `Laurent` of `Cited.lean`.
* **Proposition 3** (adelic bounds for PCF polynomials): cited. Source: P. Ingram, *A finiteness
  result for post-critically finite polynomials*, Int. Math. Res. Not. IMRN 2012, no. 3,
  524–543. Lean: the proposition `IngramBound` of `Cited.lean`, which states the bounds in
  integral form (after clearing a denominator `D`, the quantities are algebraic integers of
  bounded house).
* **Lemma 4** (one fixed linear form): proved in a different form, assuming
  `DvornicichZannier` (R. Dvornicich and U. Zannier, *Cyclotomic diophantine problems*, Duke
  Math. J. 139 (2007), Theorem L). Lean: `lemma4`.
* **Lemma 5** (Hajós' lemma): proved as stated. Lean: `lemma5`.
* **Lemma 6** (super-attracting parameters): proved in a different form, assuming
  `SuperAttracting` (the one-parameter case, cited from R. Dujardin and C. Favre,
  *Distribution of rational maps with a preperiodic critical point*, Amer. J. Math. 130 (2008),
  Theorem 2.5 and Proposition 2.4, and B. Branner and J. H. Hubbard, *The iteration of cubic
  polynomials. Part I*, Acta Math. 160 (1988)). Lean: `lemma6`.
* **Lemma 7** (high-order resultants): proved in a different form, with no cited input.
  Lean: `lemma7`.
* **Lemma 8** (removing zero coordinates): not formalized. In the derivation of Theorem 1
  (`mainStatement_of_not_isExceptional`) its role is played by a pigeonhole argument on the
  pattern of vanishing coordinates, which directly produces an exceptional family.
* **Lemma 9** (there are no exceptional families): proved as stated, assuming all four cited
  propositions. Lean: `lemma9`.
-/

namespace IngramMello

open Polynomial

/-- **Theorem 1.** Let `K` be a number field and `d ≥ 2`. There are only finitely many monic
centred PCF polynomials of degree `d` with coefficients in `K^cyc`.

Lean form: `MainStatement` of `Statements.lean`, proved assuming the four cited results
`IngramBound`, `DvornicichZannier`, `Laurent` and `SuperAttracting` of `Cited.lean`. -/
theorem theorem1 (h : CitedResults) : MainStatement :=
  mainStatement_of_not_isExceptional h.1 h.2.1 fun d hd K hK r a T =>
    not_isExceptional h.1 h.2.1 h.2.2.1 h.2.2.2 d hd K hK r a T

/-- **Lemma 4** (fixed linear form). Paper statement: let `K` be a number field and `M_v` an
adelic constant. Then there is a linear form `L(x) = e_1 x_1 + ⋯ + e_m x_m ∈ K[x]` such that
every `α ∈ K^cyc` with `|α|_w ≤ M_v` for all places can be written as `α = L(ζ_1, …, ζ_m)` with
each `ζ_i` zero or a root of unity.

Lean form: the adelic hypothesis on `α` is replaced by "`α` is an algebraic integer with house
at most `B`" (the paper's proof reduces to this case by clearing a denominator `D`, and the
formalized Proposition 3, `IngramBound`, is stated directly in this integral form). The input
is the cited `DvornicichZannier` (Theorem L of Dvornicich–Zannier). -/
theorem lemma4 (hDZ : DvornicichZannier) (K : IntermediateField ℚ ℂ)
    (hK : FiniteDimensional ℚ K) (B : ℝ) :
    ∃ (m : ℕ) (e : Fin m → ℂ), (∀ i, e i ∈ K) ∧
      ∀ α ∈ Kcyc K, IsIntegral ℤ α → HouseLE α B →
        ∃ y : Fin m → ℂ, (∀ i, y i = 0 ∨ IsRootOfUnityC (y i)) ∧ α = ∑ i, e i * y i :=
  exists_linearForm hDZ K hK B

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
is the cited `SuperAttracting`; the general case is reduced to it along a generic monomial
curve, as in the paper. -/
theorem lemma6 (hSA : SuperAttracting) {r d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → MvLaurent r)
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
    exists_superAttracting_root hSA (RingHom.id _) hd a hnc hnm rfl hBN hfg
  rw [RingHom.comp_id] at hroot hper
  exact ⟨x, c₀, q, hq, hroot, hper⟩

/-- **Lemma 7** (high-order resultants). Paper statement: let `R = ℂ[u_1^{±1}, …, u_r^{±1}]`,
let `f = z^d + a_{d-2} z^{d-2} + ⋯ + a_0 ∈ R[z]`, let `S` be the multiset of critical points of
`f` with infinite forward orbit, and `W_{ℓ,k} = ∏_{c ∈ S} (f^ℓ(c) - f^k(c))`. Then `W_{ℓ,k} ∈ R`,
`W_{ℓ,k} ≠ 0` for `ℓ ≠ k`, `W_{ℓ,k}` has coefficients in `k₀` if the `a_i` do, and if `x` is a
super-attracting parameter then there is `q` with `ord_x W_{q(ℓ+1),qℓ} ≥ ℓ + 1` for all `ℓ`.

Lean form: the coefficients live in an integrally closed `ℚ`-algebra domain `R₀` mapping to
`ℂ[u^{±1}]` by `ι` (in the paper `R₀ = k₀[u^{±1}]`, and `R₀ = R` when `k₀ = ℂ`); `f'` is
factored as `d · A · B` with `A` monic in `R₀[z]`, and the roots of `A` are exactly the
critical points with infinite orbit, so the paper's `W_{ℓ,k}` is `W A f ℓ k = Res(A, f^ℓ - f^k)`,
an element of `R₀`. A super-attracting parameter is given as `x ∈ (ℂ^×)^r`, `q ≥ 1` and a root
`c₀` of `A_x` with `f_x^q(c₀) = c₀`; the order bound then holds for this `q`. -/
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
theorem lemma9 (hIB : IngramBound) (hDZ : DvornicichZannier) (hL : Laurent)
    (hSA : SuperAttracting) (d : ℕ) (hd : 2 ≤ d) (K : IntermediateField ℚ ℂ)
    (hK : FiniteDimensional ℚ K) (r : ℕ) (a : Fin (d - 1) → AddMonoidAlgebra K (Fin r → ℤ))
    (T : Set (Fin r → ℂˣ)) : ¬ IsExceptional d K r a T :=
  not_isExceptional hIB hDZ hL hSA d hd K hK r a T

end IngramMello
