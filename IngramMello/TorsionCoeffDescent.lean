import IngramMello.LaurentOrder

/-!
# Rational equations for algebraic torus points

A nonzero complex Laurent equation on algebraic points implies a nonzero rational
Laurent equation on those points. This is the coefficient descent needed to apply
rational relations among roots of unity in the proof of Laurent's theorem.
-/

namespace IngramMello
namespace MvLaurent

open AddMonoidAlgebra
open scoped AlgebraMonoidAlgebra

variable {r : ℕ}

/-- Apply a linear functional to the coefficients, retaining complex coefficients. -/
noncomputable def mapCoeffLinear (K : IntermediateField ℚ ℂ) (L : ℂ →ₗ[K] K)
    (P : MvLaurent r) : MvLaurent r :=
  AddMonoidAlgebra.map (K.val.toAddMonoidHom.comp L.toAddMonoidHom) P

@[simp]
theorem coeff_mapCoeffLinear (K : IntermediateField ℚ ℂ) (L : ℂ →ₗ[K] K)
    (P : MvLaurent r) (e : Fin r → ℤ) :
    (mapCoeffLinear K L P).coeff e = (L (P.coeff e) : ℂ) := by
  simp [mapCoeffLinear, AddMonoidAlgebra.coeff_map]

/-- A coefficient functional commutes with evaluation at points of its scalar field. -/
theorem evalHom_mapCoeffLinear (K : IntermediateField ℚ ℂ) (L : ℂ →ₗ[K] K)
    (P : MvLaurent r) (x : Fin r → ℂˣ) (hx : ∀ j, (x j : ℂ) ∈ K) :
    evalHom x (mapCoeffLinear K L P) = (L (evalHom x P) : ℂ) := by
  induction P using AddMonoidAlgebra.induction_linear with
  | zero => simp [mapCoeffLinear]
  | add P Q hP hQ => simp [mapCoeffLinear, AddMonoidAlgebra.map_add, hP, hQ] at *
  | single e c =>
    have hm : (∏ j, (x j : ℂ) ^ e j) ∈ K :=
      K.toSubfield.prod_mem fun j _ => K.toSubfield.zpow_mem (hx j) _
    let m : K := ⟨∏ j, (x j : ℂ) ^ e j, hm⟩
    have hL := L.map_smul m c
    have hLc : (L (c * (m : ℂ)) : ℂ) = (L c : ℂ) * (m : ℂ) := by
      simpa [Algebra.smul_def, mul_comm] using congrArg (fun z : K => (z : ℂ)) hL
    simpa [mapCoeffLinear, evalHom_single, m] using hLc.symm

/-- Extract a nonzero equation with coefficients in `K`, valid on the `K`-points
of the original zero set. -/
theorem exists_equation_over (K : IntermediateField ℚ ℂ) {P : MvLaurent r}
    (hP : P ≠ 0) :
    ∃ F : MvLaurent r, F ≠ 0 ∧ (∀ e, F.coeff e ∈ K) ∧
      ∀ x : Fin r → ℂˣ, (∀ j, (x j : ℂ) ∈ K) →
        evalHom x P = 0 → evalHom x F = 0 := by
  classical
  obtain ⟨e, he⟩ : ∃ e, P.coeff e ≠ 0 := by
    by_contra! h
    exact hP (AddMonoidAlgebra.ext (Finsupp.ext h))
  obtain ⟨L, hL⟩ := Module.Projective.exists_dual_ne_zero K he
  refine ⟨mapCoeffLinear K L P, ?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun F : MvLaurent r => F.coeff e) h
    exact hL (by simpa using this)
  · intro e
    exact (L (P.coeff e)).property
  · intro x hx h
    rw [evalHom_mapCoeffLinear K L P x hx, h, map_zero]
    rfl

/-- Algebraic coefficients make a Laurent polynomial integral over the rational
Laurent ring. Negative monomials are already elements of that base ring. -/
theorem isIntegral_of_coeff (P : MvLaurent r)
    (hP : ∀ e, IsIntegral ℚ (P.coeff e)) :
    IsIntegral (AddMonoidAlgebra ℚ (Fin r → ℤ)) P := by
  let R := AddMonoidAlgebra ℚ (Fin r → ℤ)
  rw [← P.sum_coeff_single]
  apply IsIntegral.sum
  intro e he
  have hc : IsIntegral R (single (0 : Fin r → ℤ) (P.coeff e) : MvLaurent r) :=
    ((hP e).algebraMap (B := MvLaurent r)).tower_top
  have hm : IsIntegral R (single e (1 : ℂ) : MvLaurent r) := by
    simpa [R] using
      (isIntegral_algebraMap (R := R) (A := MvLaurent r) (x := single e (1 : ℚ)))
  simpa using hc.mul hm

/-- A nonzero Laurent polynomial with algebraic coefficients divides a nonzero
rational Laurent polynomial. -/
theorem exists_rational_multiple {F : MvLaurent r} (hF : F ≠ 0)
    (hcoeff : ∀ e, IsIntegral ℚ (F.coeff e)) :
    ∃ Q : AddMonoidAlgebra ℚ (Fin r → ℤ), Q ≠ 0 ∧
      F ∣ AddMonoidAlgebra.mapRingHom _ (algebraMap ℚ ℂ) Q := by
  exact (isIntegral_of_coeff F hcoeff).isAlgebraic.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hF)

/-- Every complex Laurent equation gives a rational equation containing all its
algebraic torus zeros. The rational equation remains nonzero. -/
theorem exists_rational_equation {P : MvLaurent r} (hP : P ≠ 0) :
    ∃ Q : AddMonoidAlgebra ℚ (Fin r → ℤ), Q ≠ 0 ∧
      ∀ x : Fin r → ℂˣ, (∀ j, IsAlgebraic ℚ (x j : ℂ)) →
        evalHom x P = 0 →
          evalHom x (AddMonoidAlgebra.mapRingHom _ (algebraMap ℚ ℂ) Q) = 0 := by
  obtain ⟨F, hF, hc, hz⟩ := exists_equation_over (algebraicClosure ℚ ℂ) hP
  obtain ⟨Q, hQ, G, hG⟩ := exists_rational_multiple hF hc
  refine ⟨Q, hQ, fun x hx h => ?_⟩
  rw [hG, map_mul, hz x (fun j => (hx j).isIntegral) h, zero_mul]

/-- On algebraic torus points, rational equations suffice to test density in the
whole torus. This is the dense branch in induction on the torus dimension. -/
theorem rational_dense_iff {T : Set (Fin r → ℂˣ)}
    (hT : ∀ x ∈ T, ∀ j, IsAlgebraic ℚ (x j : ℂ)) :
    (∀ Q : AddMonoidAlgebra ℚ (Fin r → ℤ),
      (∀ x ∈ T, evalHom x (AddMonoidAlgebra.mapRingHom _ (algebraMap ℚ ℂ) Q) = 0) →
        Q = 0) ↔
    (∀ P : MvLaurent r, (∀ x ∈ T, evalHom x P = 0) → P = 0) := by
  constructor
  · intro h P hP
    by_contra hn
    obtain ⟨Q, hQ, hz⟩ := exists_rational_equation hn
    exact hQ (h Q fun x hx => hz x (hT x hx) (hP x hx))
  · intro h Q hQ
    have hz := h _ hQ
    ext e
    have he := congrArg (fun P : MvLaurent r => P.coeff e) hz
    simpa using he

/-- The coefficient reduction in the point and evaluation conventions of `Laurent`.
No infinitude hypothesis is needed for this step. -/
theorem exists_rational_equation_of_torsion {T : Set (Fin r → ℂ)}
    (hT : ∀ x ∈ T, ∀ j, IsRootOfUnityC (x j))
    {P : MvLaurent r} (hP : P ≠ 0) (hz : ∀ x ∈ T, eval P x = 0) :
    ∃ Q : AddMonoidAlgebra ℚ (Fin r → ℤ), Q ≠ 0 ∧
      ∀ x ∈ T, eval (AddMonoidAlgebra.mapRingHom _ (algebraMap ℚ ℂ) Q) x = 0 := by
  obtain ⟨Q, hQ, h⟩ := exists_rational_equation hP
  refine ⟨Q, hQ, fun x hx => ?_⟩
  have hne (j) : x j ≠ 0 := by
    obtain ⟨n, hn, heq⟩ := hT x hx j
    intro hj
    simp [hj, zero_pow hn.ne'] at heq
  let u : Fin r → ℂˣ := fun j => Units.mk0 (x j) (hne j)
  have ha (j) : IsAlgebraic ℚ (u j : ℂ) := by
    obtain ⟨n, hn, heq⟩ := hT x hx j
    exact (IsIntegral.of_pow hn (heq ▸ isIntegral_one (R := ℚ))).isAlgebraic
  simpa [evalHom_apply, u] using h u ha (by simpa [evalHom_apply, u] using hz x hx)

end MvLaurent
end IngramMello
