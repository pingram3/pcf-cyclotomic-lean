import Mathlib
import IngramMello.Inputs

/-!
# Places of a finite extension of `ℂ(t)` over `t = 0` and `t = ∞`

Infrastructure for the proof of `SuperAttracting` (Lemma 6 of the paper in the one-parameter
case).

* `exists_valuation_of_prime`: a nonzero prime `𝔭` of a Dedekind domain `A` with
  fraction field `K` extends to a `ℤᵐ⁰`-valued valuation of any finite extension `E` of `K`
  (via a prime of the integral closure of `A` in `E` lying over `𝔭`).
* `TwoPlaces w₀ w₁`: the properties of two places of `E ⊇ ℂ(t)` over `t = 0` and `t = ∞`,
  normalized so that `w₀(t) · w₁(t) = 1`; `exists_twoPlaces` constructs them.
* `TwoPlaces.mem_range_C_of_le_one` (an `x ∈ ℂ[t,t⁻¹]` integral at both places is constant)
  and `TwoPlaces.val_mul_val_eq_one_of_forall_eval_ne_zero` (a unit `λ tⁿ` of `ℂ[t,t⁻¹]` has
  `w₀(x) w₁(x) = 1`).
-/

namespace IngramMello

open Polynomial LaurentPolynomial

/-! ### Extension of a discrete place to a finite extension -/

section Dedekind

/-- **Extension of a place.** A nonzero prime `𝔭` of a Dedekind domain `A` with fraction field
`K` extends to a `ℤᵐ⁰`-valued valuation `w` of a finite separable extension `E` of `K`:
`w ≤ 1` on `A` and `w < 1` exactly on `𝔭`. -/
theorem exists_valuation_of_prime (A : Type*) [CommRing A] [IsDedekindDomain A]
    (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
    (E : Type*) [Field E] [Algebra K E] [Algebra A E] [IsScalarTower A K E]
    [FiniteDimensional K E] [Algebra.IsSeparable K E]
    (𝔭 : Ideal A) [𝔭.IsPrime] (h𝔭 : 𝔭 ≠ ⊥) :
    ∃ w : Valuation E (WithZero (Multiplicative ℤ)),
      (∀ x : A, w (algebraMap A E x) ≤ 1) ∧ ∀ x : A, w (algebraMap A E x) < 1 ↔ x ∈ 𝔭 := by
  haveI : IsDedekindDomain (integralClosure A E) := integralClosure.isDedekindDomain A K E
  haveI : IsFractionRing (integralClosure A E) E :=
    integralClosure.isFractionRing_of_finite_extension K E
  have hinjE : Function.Injective (algebraMap A E) := by
    rw [IsScalarTower.algebraMap_eq A K E]
    exact (algebraMap K E).injective.comp (IsFractionRing.injective A K)
  have hinj : Function.Injective (algebraMap A (integralClosure A E)) := by
    intro x y hxy
    apply hinjE
    rw [IsScalarTower.algebraMap_apply A (integralClosure A E) E,
      IsScalarTower.algebraMap_apply A (integralClosure A E) E y, hxy]
  obtain ⟨Q, -, hQp, hQ⟩ := Ideal.exists_ideal_over_prime_of_isIntegral 𝔭
    (⊥ : Ideal (integralClosure A E)) (Ideal.comap_bot_le_of_injective _ hinj)
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    exact h𝔭 (by rw [← hQ, Ideal.under, Ideal.comap_bot_of_injective _ hinj])
  let v : IsDedekindDomain.HeightOneSpectrum (integralClosure A E) := ⟨Q, hQp, hQne⟩
  refine ⟨v.valuation E, fun x => ?_, fun x => ?_⟩
  · rw [IsScalarTower.algebraMap_apply A (integralClosure A E) E]
    exact v.valuation_le_one _
  · rw [IsScalarTower.algebraMap_apply A (integralClosure A E) E, v.valuation_lt_one_iff_mem]
    change _ ∈ Q ↔ _
    rw [← hQ]
    rfl

end Dedekind

/-! ### Powers of valuations and a normalization lemma in `ℤᵐ⁰` -/

section Pow

variable {F Γ₀ : Type*} [Field F] [LinearOrderedCommGroupWithZero Γ₀]

/-- The valuation `x ↦ (w x)^n`, `n ≠ 0`. -/
noncomputable def valPow (w : Valuation F Γ₀) {n : ℕ} (hn : n ≠ 0) : Valuation F Γ₀ :=
  w.map (powMonoidWithZeroHom hn) fun _ _ h => pow_le_pow_left' h n

@[simp] theorem valPow_apply (w : Valuation F Γ₀) {n : ℕ} (hn : n ≠ 0) (x : F) :
    valPow w hn x = w x ^ n := rfl

/-- In `ℤᵐ⁰`, for `α < 1 < β` nonzero there are positive `e, e'` with `α^e' β^e = 1`. -/
theorem exists_pow_mul_pow_eq_one {α β : WithZero (Multiplicative ℤ)} (hα0 : α ≠ 0)
    (hα : α < 1) (hβ : 1 < β) :
    ∃ e e' : ℕ, e ≠ 0 ∧ e' ≠ 0 ∧ α ^ e' * β ^ e = 1 := by
  have hβ0 : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  obtain ⟨a, rfl⟩ : ∃ a, α = WithZero.exp a := ⟨_, (WithZero.exp_log hα0).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, β = WithZero.exp b := ⟨_, (WithZero.exp_log hβ0).symm⟩
  rw [WithZero.exp_lt_one_iff] at hα
  rw [WithZero.one_lt_exp_iff] at hβ
  refine ⟨(-a).toNat, b.toNat, ?_, ?_, ?_⟩
  · rw [Ne, Int.toNat_eq_zero]; omega
  · rw [Ne, Int.toNat_eq_zero]; omega
  · rw [← WithZero.exp_nsmul, ← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero]
    congr 1
    simp only [nsmul_eq_mul]
    rw [Int.toNat_of_nonneg (by omega), Int.toNat_of_nonneg (by omega)]
    ring

end Pow

/-! ### The two places of a finite extension of `ℂ(t)` -/

/-- A fraction field of a localization of a domain `R` (at non-zero-divisors) is a fraction
field of `R`. -/
theorem isFractionRing_of_isLocalization_of_isFractionRing {R S T : Type*} [CommRing R]
    [IsDomain R] [CommRing S] [IsDomain S] [CommRing T] [Algebra R S] [Algebra R T]
    [Algebra S T] [IsScalarTower R S T] (M : Submonoid R) [IsLocalization M S]
    (hM : M ≤ nonZeroDivisors R) [IsFractionRing S T] : IsFractionRing R T := by
  have hinj : Function.Injective (algebraMap R S) := IsLocalization.injective S hM
  have h := IsLocalization.localization_localization_isLocalization M (nonZeroDivisors S) T
  have heq : IsLocalization.localizationLocalizationSubmodule M (nonZeroDivisors S)
      = nonZeroDivisors R := by
    ext x
    rw [IsLocalization.mem_localizationLocalizationSubmodule, mem_nonZeroDivisors_iff_ne_zero]
    constructor
    · rintro ⟨y, z, e⟩ hx
      rw [hx, map_zero] at e
      exact mul_ne_zero (nonZeroDivisors.ne_zero y.2) (IsLocalization.map_units S z).ne_zero
        e.symm
    · intro hx
      refine ⟨⟨algebraMap R S x, mem_nonZeroDivisors_of_ne_zero ?_⟩, 1, by simp⟩
      intro h
      exact hx (hinj (by rw [h, map_zero]))
  rw [heq] at h
  exact h

section FunctionField

/-- `ℂ(t)`, as the fraction field of `ℂ[t,t⁻¹]`. -/
abbrev Kt : Type := FractionRing (LaurentPolynomial ℂ)

variable (E : Type*) [Field E] [Algebra Kt E] [FiniteDimensional Kt E]
  [Algebra (LaurentPolynomial ℂ) E] [IsScalarTower (LaurentPolynomial ℂ) Kt E]

/-- A place of `E` attached to a presentation `ψ : ℂ[X] → ℂ[t,t⁻¹]` of `ℂ[t,t⁻¹]` as the
localization of `ℂ[X]` at the powers of `X` (we use `X ↦ t` and `X ↦ t⁻¹`). -/
theorem exists_place_of_ringHom (ψ : ℂ[X] →+* LaurentPolynomial ℂ)
    (hψ : @IsLocalization ℂ[X] _ (Submonoid.powers X) (LaurentPolynomial ℂ) _ ψ.toAlgebra) :
    ∃ w : Valuation E (WithZero (Multiplicative ℤ)),
      (∀ p : ℂ[X], w (algebraMap (LaurentPolynomial ℂ) E (ψ p)) ≤ 1) ∧
      ∀ p : ℂ[X], w (algebraMap (LaurentPolynomial ℂ) E (ψ p)) < 1 ↔ p.coeff 0 = 0 := by
  letI : Algebra ℂ[X] (LaurentPolynomial ℂ) := ψ.toAlgebra
  letI : Algebra ℂ[X] E := ((algebraMap (LaurentPolynomial ℂ) E).comp ψ).toAlgebra
  haveI : IsScalarTower ℂ[X] Kt E := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply ℂ[X] (LaurentPolynomial ℂ) Kt x,
      ← IsScalarTower.algebraMap_apply (LaurentPolynomial ℂ) Kt E]
    rfl
  haveI : IsFractionRing ℂ[X] Kt :=
    isFractionRing_of_isLocalization_of_isFractionRing (S := LaurentPolynomial ℂ)
      (Submonoid.powers X) (powers_le_nonZeroDivisors_of_noZeroDivisors X_ne_zero)
  haveI : CharZero Kt := charZero_of_injective_ringHom
    ((algebraMap (LaurentPolynomial ℂ) Kt).comp LaurentPolynomial.C).injective
  haveI : (Ideal.span {(X : ℂ[X])}).IsPrime :=
    (Ideal.span_singleton_prime X_ne_zero).mpr prime_X
  obtain ⟨w, h1, h2⟩ := exists_valuation_of_prime ℂ[X] Kt E (Ideal.span {X})
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_ne_zero)
  refine ⟨w, fun p => h1 p, fun p => ?_⟩
  exact (h2 p).trans (by rw [Ideal.mem_span_singleton, X_dvd_iff])

/-- The properties of two places `w₀`, `w₁` of `E` over `t = 0` and `t = ∞`, normalized so
that `w₀(t) · w₁(t) = 1`. -/
structure TwoPlaces (w₀ w₁ : Valuation E (WithZero (Multiplicative ℤ))) : Prop where
  le₀ : ∀ p : ℂ[X], w₀ (algebraMap (LaurentPolynomial ℂ) E (toLaurent p)) ≤ 1
  lt₀ : ∀ p : ℂ[X], w₀ (algebraMap (LaurentPolynomial ℂ) E (toLaurent p)) < 1 ↔ p.coeff 0 = 0
  le₁ : ∀ p : ℂ[X], w₁ (algebraMap (LaurentPolynomial ℂ) E (invert (toLaurent p))) ≤ 1
  lt₁ : ∀ p : ℂ[X],
    w₁ (algebraMap (LaurentPolynomial ℂ) E (invert (toLaurent p))) < 1 ↔ p.coeff 0 = 0
  T_lt : w₀ (algebraMap (LaurentPolynomial ℂ) E (T 1)) < 1
  T_mul : w₀ (algebraMap (LaurentPolynomial ℂ) E (T 1)) *
    w₁ (algebraMap (LaurentPolynomial ℂ) E (T 1)) = 1

/-- **Two places.** Every finite extension `E` of `ℂ(t)` has normalized places over `0`, `∞`. -/
theorem exists_twoPlaces : ∃ w₀ w₁ : Valuation E (WithZero (Multiplicative ℤ)),
    TwoPlaces E w₀ w₁ := by
  -- the place over `t = 0`
  set ψ₀ : ℂ[X] →+* LaurentPolynomial ℂ :=
    (RingEquiv.refl (LaurentPolynomial ℂ)).toRingHom.comp (algebraMap ℂ[X] (LaurentPolynomial ℂ))
    with hψ₀
  have hψ₀' : ∀ p, ψ₀ p = toLaurent p := fun p => rfl
  obtain ⟨u₀, hu₀le, hu₀lt⟩ := exists_place_of_ringHom E ψ₀
    ((IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers X)
      (RingEquiv.refl (LaurentPolynomial ℂ))).mp LaurentPolynomial.isLocalization)
  -- the place over `t = ∞`
  set ψ₁ : ℂ[X] →+* LaurentPolynomial ℂ :=
    (invert (R := ℂ)).toRingEquiv.toRingHom.comp (algebraMap ℂ[X] (LaurentPolynomial ℂ))
    with hψ₁
  have hψ₁' : ∀ p, ψ₁ p = invert (toLaurent p) := fun p => rfl
  obtain ⟨u₁, hu₁le, hu₁lt⟩ := exists_place_of_ringHom E ψ₁
    ((IsLocalization.isLocalization_iff_of_ringEquiv (Submonoid.powers X)
      (invert (R := ℂ)).toRingEquiv).mp LaurentPolynomial.isLocalization)
  simp only [hψ₀'] at hu₀le hu₀lt
  simp only [hψ₁'] at hu₁le hu₁lt
  -- `u₀(t) < 1 < u₁(t)`
  have hT0 : u₀ (algebraMap (LaurentPolynomial ℂ) E (T 1)) < 1 := by
    have := (hu₀lt X).mpr (by simp)
    rwa [Polynomial.toLaurent_X] at this
  have hTinv : u₁ (algebraMap (LaurentPolynomial ℂ) E (T (-1))) < 1 := by
    have := (hu₁lt X).mpr (by simp)
    rwa [Polynomial.toLaurent_X, invert_T] at this
  have hTT : algebraMap (LaurentPolynomial ℂ) E (T 1) * algebraMap (LaurentPolynomial ℂ) E (T (-1))
      = 1 := by
    rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  have hT1ne : algebraMap (LaurentPolynomial ℂ) E (T 1) ≠ 0 := left_ne_zero_of_mul_eq_one hTT
  have hTinv_eq : algebraMap (LaurentPolynomial ℂ) E (T (-1))
      = (algebraMap (LaurentPolynomial ℂ) E (T 1))⁻¹ := eq_inv_of_mul_eq_one_right hTT
  have hT₁ : 1 < u₁ (algebraMap (LaurentPolynomial ℂ) E (T 1)) := by
    rw [hTinv_eq, map_inv₀, inv_lt_one₀] at hTinv
    · exact hTinv
    · exact zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hT1ne)
  have hu₀T0 : u₀ (algebraMap (LaurentPolynomial ℂ) E (T 1)) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hT1ne
  obtain ⟨e, e', he, he', hee'⟩ := exists_pow_mul_pow_eq_one hu₀T0 hT0 hT₁
  refine ⟨valPow u₀ he', valPow u₁ he, ⟨fun p => ?_, fun p => ?_, fun p => ?_, fun p => ?_, ?_, ?_⟩⟩
  · rw [valPow_apply, pow_le_one_iff he']; exact hu₀le p
  · rw [valPow_apply, pow_lt_one_iff he']; exact hu₀lt p
  · rw [valPow_apply, pow_le_one_iff he]; exact hu₁le p
  · rw [valPow_apply, pow_lt_one_iff he]; exact hu₁lt p
  · rw [valPow_apply, pow_lt_one_iff he']; exact hT0
  · rw [valPow_apply, valPow_apply]; exact hee'

/-! ### Restriction of the two places to `ℂ[t,t⁻¹]` -/

variable {E}

/-- `ι(T n) = ι(T 1)^n` in `E`. -/
theorem algebraMap_T_zpow (n : ℤ) :
    algebraMap (LaurentPolynomial ℂ) E (T n) = algebraMap (LaurentPolynomial ℂ) E (T 1) ^ n := by
  have hTT : algebraMap (LaurentPolynomial ℂ) E (T 1) * algebraMap (LaurentPolynomial ℂ) E (T (-1))
      = 1 := by
    rw [← map_mul, ← T_add, add_neg_cancel, T_zero, map_one]
  have hT1ne : algebraMap (LaurentPolynomial ℂ) E (T 1) ≠ 0 := left_ne_zero_of_mul_eq_one hTT
  have hTinv_eq : algebraMap (LaurentPolynomial ℂ) E (T (-1))
      = (algebraMap (LaurentPolynomial ℂ) E (T 1))⁻¹ := eq_inv_of_mul_eq_one_right hTT
  induction n using Int.induction_on with
  | zero => simp [T_zero]
  | succ i ih => rw [T_add, map_mul, ih, zpow_add_one₀ hT1ne]
  | pred i ih => rw [T_sub, map_mul, ih, zpow_sub_one₀ hT1ne, hTinv_eq]

/-- Every nonzero Laurent polynomial is `tⁿ · p(t)` with `p(0) ≠ 0`. -/
theorem exists_T_zpow_mul_toLaurent (x : LaurentPolynomial ℂ) (hx : x ≠ 0) :
    ∃ (n : ℤ) (p : ℂ[X]), p.coeff 0 ≠ 0 ∧ x = T n * toLaurent p := by
  obtain ⟨m, f, hf⟩ := exists_T_pow x
  have hf0 : f ≠ 0 := by
    rintro rfl
    rw [map_zero] at hf
    exact hx ((mul_eq_zero.mp hf.symm).resolve_right (isUnit_T m).ne_zero)
  obtain ⟨q, hq, hXq⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd f hf0 0
  rw [C_0, sub_zero] at hq hXq
  set a := rootMultiplicity 0 f with ha
  refine ⟨(a : ℤ) - m, q, ?_, ?_⟩
  · rwa [X_dvd_iff] at hXq
  · have hx' : x = toLaurent f * T (-m) := by
      rw [hf, mul_assoc, ← T_add, add_neg_cancel, T_zero, mul_one]
    rw [hx', hq, map_mul, map_pow, Polynomial.toLaurent_X, T_pow, mul_one, T_sub]
    ring

/-- `toLaurent p = invert (toLaurent (reverse p)) · t^{deg p}`. -/
theorem toLaurent_eq_invert_reverse_mul (p : ℂ[X]) :
    toLaurent p = invert (toLaurent p.reverse) * T (p.natDegree : ℤ) := by
  have h := congrArg invert (toLaurent_reverse p)
  rw [map_mul, invert_T, involutive_invert (toLaurent p)] at h
  rw [h, mul_assoc, ← T_add, neg_add_cancel, T_zero, mul_one]

variable {w₀ w₁ : Valuation E (WithZero (Multiplicative ℤ))}

theorem TwoPlaces.T_pos (h : TwoPlaces E w₀ w₁) :
    0 < w₀ (algebraMap (LaurentPolynomial ℂ) E (T 1)) :=
  zero_lt_iff.mpr (left_ne_zero_of_mul_eq_one h.T_mul)

theorem TwoPlaces.T_eq_inv (h : TwoPlaces E w₀ w₁) :
    w₁ (algebraMap (LaurentPolynomial ℂ) E (T 1)) =
      (w₀ (algebraMap (LaurentPolynomial ℂ) E (T 1)))⁻¹ :=
  eq_inv_of_mul_eq_one_right h.T_mul

/-- The valuations of `x ≠ 0` at the two places, read off from `x = tⁿ p(t)`. -/
theorem TwoPlaces.exists_val_eq (h : TwoPlaces E w₀ w₁) {x : LaurentPolynomial ℂ} (hx : x ≠ 0) :
    ∃ (n : ℤ) (p : ℂ[X]), p.coeff 0 ≠ 0 ∧ x = T n * toLaurent p ∧
      w₀ (algebraMap (LaurentPolynomial ℂ) E x) =
        w₀ (algebraMap (LaurentPolynomial ℂ) E (T 1)) ^ n ∧
      w₁ (algebraMap (LaurentPolynomial ℂ) E x) =
        w₁ (algebraMap (LaurentPolynomial ℂ) E (T 1)) ^ (n + p.natDegree) := by
  obtain ⟨n, p, hp0, hx⟩ := exists_T_zpow_mul_toLaurent x hx
  refine ⟨n, p, hp0, hx, ?_, ?_⟩
  · have h1 : w₀ (algebraMap (LaurentPolynomial ℂ) E (toLaurent p)) = 1 :=
      (h.le₀ p).lt_or_eq.resolve_left (by rw [h.lt₀]; exact hp0)
    rw [hx, map_mul, map_mul, h1, mul_one, algebraMap_T_zpow, map_zpow₀]
  · have hpne : p ≠ 0 := by rintro rfl; exact hp0 (coeff_zero 0)
    have h1 : w₁ (algebraMap (LaurentPolynomial ℂ) E (invert (toLaurent p.reverse))) = 1 :=
      (h.le₁ p.reverse).lt_or_eq.resolve_left
        (by rw [h.lt₁, coeff_zero_reverse]; exact leadingCoeff_ne_zero.mpr hpne)
    have hne : w₁ (algebraMap (LaurentPolynomial ℂ) E (T 1)) ≠ 0 :=
      right_ne_zero_of_mul_eq_one h.T_mul
    rw [hx, toLaurent_eq_invert_reverse_mul, map_mul, map_mul, map_mul, map_mul, h1, one_mul,
      algebraMap_T_zpow, algebraMap_T_zpow (p.natDegree : ℤ), map_zpow₀, map_zpow₀,
      ← zpow_add₀ hne]

/-- Both places are trivial on the nonzero natural numbers (hence on `ℚ`). -/
theorem TwoPlaces.val_natCast (h : TwoPlaces E w₀ w₁) {N : ℕ} (hN : N ≠ 0) :
    w₀ (N : E) = 1 ∧ w₁ (N : E) = 1 := by
  have h1 : (N : E) = algebraMap (LaurentPolynomial ℂ) E (toLaurent (N : ℂ[X])) := by
    rw [map_natCast, map_natCast]
  have h2 : (N : E) = algebraMap (LaurentPolynomial ℂ) E (invert (toLaurent (N : ℂ[X]))) := by
    rw [map_natCast, map_natCast, map_natCast]
  have hc : ((N : ℂ[X]).coeff 0) ≠ 0 := by rw [natCast_coeff_zero]; exact_mod_cast hN
  constructor
  · rw [h1]; exact (h.le₀ _).lt_or_eq.resolve_left (by rw [h.lt₀]; exact hc)
  · rw [h2]; exact (h.le₁ _).lt_or_eq.resolve_left (by rw [h.lt₁]; exact hc)

/-- A Laurent polynomial integral at both places is constant. -/
theorem TwoPlaces.mem_range_C_of_le_one (h : TwoPlaces E w₀ w₁) {x : LaurentPolynomial ℂ}
    (h0 : w₀ (algebraMap (LaurentPolynomial ℂ) E x) ≤ 1)
    (h₁ : w₁ (algebraMap (LaurentPolynomial ℂ) E x) ≤ 1) :
    x ∈ Set.range (LaurentPolynomial.C : ℂ →+* LaurentPolynomial ℂ) := by
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  obtain ⟨n, p, hp0, hxe, hv0, hv₁⟩ := h.exists_val_eq hx
  rw [hv0, zpow_le_one_iff_right_of_lt_one₀ h.T_pos h.T_lt] at h0
  rw [hv₁, h.T_eq_inv, inv_zpow', zpow_le_one_iff_right_of_lt_one₀ h.T_pos h.T_lt] at h₁
  have hn : n = 0 := by omega
  have hdeg : p.natDegree = 0 := by omega
  refine ⟨p.coeff 0, ?_⟩
  rw [hxe, hn, T_zero, one_mul, eq_C_of_natDegree_eq_zero hdeg, Polynomial.toLaurent_C,
    coeff_C_zero]

/-- A nonzero Laurent polynomial with no zero in `ℂˣ` is `λ tⁿ`, and then
`w₀(x) · w₁(x) = 1`. -/
theorem TwoPlaces.val_mul_val_eq_one_of_forall_eval_ne_zero (h : TwoPlaces E w₀ w₁)
    {x : LaurentPolynomial ℂ} (hx : x ≠ 0)
    (hroot : ∀ t₀ : ℂˣ, LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀ x ≠ 0) :
    w₀ (algebraMap (LaurentPolynomial ℂ) E x) * w₁ (algebraMap (LaurentPolynomial ℂ) E x) = 1 := by
  obtain ⟨n, p, hp0, hxe, hv0, hv₁⟩ := h.exists_val_eq hx
  have hdeg : p.natDegree = 0 := by
    by_contra hdeg
    have hdeg' : p.degree ≠ 0 := by
      intro h0
      exact hdeg (natDegree_eq_of_degree_eq_some h0)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root p hdeg'
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact hp0 (by rw [coeff_zero_eq_eval_zero]; exact hz)
    apply hroot (Units.mk0 z hz0)
    rw [hxe, map_mul, eval₂_T, eval₂_toLaurent]
    simp only [Units.val_mk0]
    rw [show Polynomial.eval₂ (RingHom.id ℂ) z p = p.eval z from rfl, hz.eq_zero, mul_zero]
  rw [hv0, hv₁, hdeg, Nat.cast_zero, add_zero, ← mul_zpow, h.T_mul, one_zpow]

end FunctionField

end IngramMello
