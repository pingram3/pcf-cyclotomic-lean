import IngramMello.Descent
import IngramMello.LinearForm

/-!
# Theorem 1 from Lemma 9

The paper derives Theorem 1 from Lemmas 4, 8 and 9. Lemma 8 (removing zero
coordinates) is not needed here: after writing the coefficients with one fixed linear
form, a finite pigeonhole on the pattern of zero coordinates leaves an infinite set on
which the same coordinates vanish. Deleting them gives an exceptional family whose
coefficients are linear forms in the remaining torus coordinates.
-/

namespace IngramMello

open Polynomial

/-- **Theorem 1, assuming Lemma 9** (no exceptional families). -/
theorem mainStatement_of_not_isExceptional (hIB : IngramBound) (hDZ : DvornicichZannier)
    (hExc : ∀ d, 2 ≤ d → ∀ K : IntermediateField ℚ ℂ, FiniteDimensional ℚ K → ∀ r a T,
      ¬ IsExceptional d K r a T) : MainStatement := by
  classical
  intro K hK d hd
  by_contra hS
  set S := {a : Fin (d - 1) → ℂ | (∀ i, a i ∈ Kcyc K) ∧ IsPCF (monicCentred d a)}
  obtain ⟨D, hD, M, hM⟩ := hIB d hd
  obtain ⟨m, e, he, hlin⟩ := exists_linearForm hDZ K hK M
  have hDne : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  -- representations of the scaled coefficients
  have hrep : ∀ a ∈ S, ∀ i, ∃ y : Fin m → ℂ, (∀ j, y j = 0 ∨ IsRootOfUnityC (y j)) ∧
      (D : ℂ) * a i = ∑ j, e j * y j := by
    intro a ha i
    have halg : ∀ i, IsAlgebraic ℚ (a i) := fun i => isAlgebraic_of_mem_Kcyc K (ha.1 i)
    have hb := (hM a halg ha.2).1 i
    exact hlin _ ((Kcyc K).mul_mem ((Kcyc K).natCast_mem D) (ha.1 i)) hb.1 hb.2
  choose! Y hY0 hYsum using hrep
  let ι := Fin (d - 1) × Fin m
  let Yf : (Fin (d - 1) → ℂ) → ι → ℂ := fun a p => Y a p.1 p.2
  -- pigeonhole on the zero pattern
  have hSinf : Infinite S := Set.infinite_coe_iff.mpr hS
  obtain ⟨P, hP⟩ := Finite.exists_infinite_fiber
    (fun a : S => (fun p : ι => Yf a p = 0))
  set S' : Set (Fin (d - 1) → ℂ) := {a | a ∈ S ∧ ∀ p, (Yf a p = 0 ↔ P p)} with hS'
  have hS'inf : S'.Infinite := by
    refine Set.infinite_of_injective_forall_mem (f := fun x : ((fun a : S =>
      (fun p : ι => Yf a p = 0)) ⁻¹' {P}) => (x.1.1 : Fin (d - 1) → ℂ)) ?_ ?_
    · intro x y hxy
      exact Subtype.ext (Subtype.ext hxy)
    · intro x
      refine ⟨x.1.2, fun p => ?_⟩
      have h2 : (fun p : ι => Yf x.1 p = 0) = P := x.2
      exact iff_of_eq (congrFun h2 p)
  let J := {p : ι // ¬ P p}
  let r := Fintype.card J
  let σ := Fintype.equivFin J
  let coef : ι → K := fun p => ⟨e p.2 / D, K.div_mem (he _) (K.natCast_mem D)⟩
  let fam : Fin (d - 1) → AddMonoidAlgebra K (Fin r → ℤ) := fun i =>
    ∑ p : J, if p.1.1 = i then AddMonoidAlgebra.single (Pi.single (σ p) 1) (coef p.1) else 0
  let pt : (Fin (d - 1) → ℂ) → Fin r → ℂˣ := fun a k =>
    if h : Yf a (σ.symm k).1 ≠ 0 then Units.mk0 _ h else 1
  have hpt : ∀ a ∈ S', ∀ k, (pt a k : ℂ) = Yf a (σ.symm k).1 := by
    intro a ha k
    have : Yf a (σ.symm k).1 ≠ 0 := fun h0 => (σ.symm k).2 ((ha.2 _).1 h0)
    simp [pt, this]
  have heval : ∀ a ∈ S', (fun i => MvLaurent.evalOver K (pt a) (fam i)) = a := by
    intro a ha
    funext i
    simp only [fam, map_sum, apply_ite (MvLaurent.evalOver K (pt a)), map_zero,
      evalOver_single_basis, hpt a ha, Equiv.symm_apply_apply]
    let g : ι → ℂ := fun p => if p.1 = i then ((coef p : K) : ℂ) * Yf a p else 0
    change ∑ p : J, g p.1 = a i
    have hsplit := Fintype.sum_subtype_add_sum_subtype P g
    rw [Finset.sum_eq_zero (fun p _ => by simp [g, (ha.2 p.1).2 p.2]), zero_add] at hsplit
    change ∑ p : {p : ι // ¬ P p}, g p.1 = a i
    rw [hsplit, Fintype.sum_prod_type, Finset.sum_eq_single i (fun b _ hb => by simp [g, hb])
      (by simp)]
    simp only [g, ite_true, coef, Yf]
    have h1 := hYsum a ha.1 i
    simp_rw [div_mul_eq_mul_div, ← Finset.sum_div, ← h1]
    field_simp
  have hinj : Set.InjOn pt S' := by
    intro a ha b hb hab
    rw [← heval a ha, ← heval b hb, hab]
  refine hExc d hd K hK r fam (pt '' S') ⟨hS'inf.image hinj, ?_, ?_, ?_⟩
  · rintro _ ⟨a, ha, rfl⟩ k
    rw [hpt a ha]
    exact (hY0 a ha.1 _ _).resolve_left fun h0 => (σ.symm k).2 ((ha.2 _).1 h0)
  · rintro _ ⟨a, ha, rfl⟩
    rw [heval a ha]
    exact ha.1.2
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab
    have : a = b := by
      have := hab
      simp only at this
      rw [heval a ha, heval b hb] at this
      exact this
    rw [this]
end IngramMello
