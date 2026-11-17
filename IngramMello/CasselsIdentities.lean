import IngramMello.CasselsDecomposition

/-!
# Cassels' trace identities

For a prime `p` and `P = p * P₁`, the relative trace `Tr_{F_P/F_{P₁}}` of powers of the
generator, and the two identities of Cassels relating `M_P` to `M_{P₁}` (equations (2.4) and
(2.8) of Loxton's paper).
-/

namespace IngramMello

open Polynomial IntermediateField Module

/-! ### Minimal polynomials and traces of generators (generic) -/

/-- **Minimal polynomial of a generator.** If `x` generates `L` over `K` and `q` is a monic
polynomial of degree `[L : K]` vanishing at `x`, then `q` is the minimal polynomial of `x` and
the trace of `x`
is `-q.nextCoeff`. -/
theorem minpoly_eq_of_adjoin_eq_top {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {x : L} (htop : K⟮x⟯ = ⊤) {q : K[X]} (hq : q.Monic)
    (hroot : aeval x q = 0) (hdeg : q.natDegree = finrank K L) :
    minpoly K x = q ∧ Algebra.trace K L x = -q.nextCoeff := by
  have hx : IsIntegral K x := IsIntegral.of_finite K x
  have hdvd : minpoly K x ∣ q := minpoly.dvd K x hroot
  have hnat : (minpoly K x).natDegree = finrank K L := by
    rw [← adjoin.finrank hx, htop, finrank_top']
  have hmin : minpoly K x = q :=
    (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hx) hq hdvd (by rw [hnat, hdeg])).symm
  refine ⟨hmin, ?_⟩
  rw [trace_eq_finrank_mul_minpoly_nextCoeff, htop, IntermediateField.finrank_top, hmin]
  simp

/-! ### The tower `F_{P₁} ⊆ F_P` -/

section Tower

variable {P₁ P : ℕ}

/-- The `F_{P₁}`-algebra structure on `F_P` for `P₁ ∣ P`. -/
noncomputable abbrev towerAlgebra (hP : 0 < P) (hdvd : P₁ ∣ P) :
    Algebra (cycField P₁) (cycField P) :=
  (IntermediateField.inclusion (cycField_mono hP hdvd)).toRingHom.toAlgebra

theorem towerAlgebra_algebraMap_apply (hP : 0 < P) (hdvd : P₁ ∣ P) (y : cycField P₁) :
    ((@algebraMap _ _ _ _ (towerAlgebra hP hdvd) y : cycField P) : ℂ) = y :=
  coe_inclusion _ y

theorem towerAlgebra_isScalarTower' (hP : 0 < P) (hdvd : P₁ ∣ P) :
    @IsScalarTower (cycField P₁) (cycField P) ℂ (towerAlgebra hP hdvd).toSMul _ _ := by
  let _ := towerAlgebra hP hdvd
  exact IsScalarTower.of_algebraMap_eq fun y => by
    rw [IntermediateField.algebraMap_apply, IntermediateField.algebraMap_apply,
      towerAlgebra_algebraMap_apply]

theorem towerAlgebra_isScalarTower (hP : 0 < P) (hdvd : P₁ ∣ P) :
    @IsScalarTower ℚ (cycField P₁) (cycField P) _ (towerAlgebra hP hdvd).toSMul _ := by
  let _ := towerAlgebra hP hdvd
  exact IsScalarTower.of_algebraMap_eq fun q =>
    ((IntermediateField.inclusion (cycField_mono hP hdvd)).commutes q).symm

end Tower

section Generic

variable {P₁ P : ℕ}
variable [Algebra (cycField P₁) (cycField P)] [IsScalarTower ℚ (cycField P₁) (cycField P)]
  [IsScalarTower (cycField P₁) (cycField P) ℂ]

omit [IsScalarTower ℚ (cycField P₁) (cycField P)] in
theorem coe_algebraMap_cycField (y : cycField P₁) :
    ((algebraMap (cycField P₁) (cycField P) y : cycField P) : ℂ) = y := by
  have := IsScalarTower.algebraMap_apply (cycField P₁) (cycField P) ℂ y
  simpa using this.symm

instance cycField_tower_finiteDimensional : FiniteDimensional (cycField P₁) (cycField P) :=
  FiniteDimensional.right ℚ (cycField P₁) (cycField P)

omit [IsScalarTower (cycField P₁) (cycField P) ℂ] in
theorem totient_mul_finrank_cycField (hP : 0 < P) (hdvd : P₁ ∣ P) :
    Nat.totient P₁ * finrank (cycField P₁) (cycField P) = Nat.totient P := by
  have hP₁ : 0 < P₁ := Nat.pos_of_dvd_of_pos hdvd hP
  rw [← cycField_finrank hP₁, ← cycField_finrank hP]
  exact Module.finrank_mul_finrank ℚ (cycField P₁) (cycField P)

/-- **Generators of `F_P` over `F_{P₁}`.** If `ζ_P = x^a · η^b` with `η ∈ F_{P₁}`, then `x`
generates `F_P` over `F_{P₁}`. -/
theorem adjoin_eq_top_of_zetaC_eq (hP : 0 < P) (x : cycField P) (η : cycField P₁) (a b : ℤ)
    (h : zetaC P = (x : ℂ) ^ a * (η : ℂ) ^ b) : (cycField P₁)⟮x⟯ = ⊤ := by
  let g : cycField P := AdjoinSimple.gen ℚ (zetaC P)
  have hg : g ∈ (cycField P₁)⟮x⟯ := by
    have hgx : g = x ^ a * (algebraMap (cycField P₁) (cycField P) η) ^ b := by
      apply Subtype.ext
      have e1 : ∀ z : cycField P, ∀ n : ℤ, ((z ^ n : cycField P) : ℂ) = (z : ℂ) ^ n := by
        intro z n
        exact map_zpow₀ (cycField P).val z n
      simp only [g, AdjoinSimple.coe_gen, h]
      rw [IntermediateField.coe_mul, e1, e1, coe_algebraMap_cycField]
    rw [hgx]
    exact mul_mem (zpow_mem (mem_adjoin_simple_self _ x) a)
      (zpow_mem (IntermediateField.algebraMap_mem _ η) b)
  have htop : Algebra.adjoin ℚ ({g} : Set (cycField P)) = ⊤ := by
    have := PowerBasis.adjoin_gen_eq_top (adjoin.powerBasis (zetaC_isIntegral hP))
    rwa [adjoin.powerBasis_gen] at this
  have hle : Algebra.adjoin ℚ ({g} : Set (cycField P)) ≤
      ((cycField P₁)⟮x⟯.restrictScalars ℚ).toSubalgebra := by
    rw [Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    exact hg
  rw [eq_top_iff]
  intro y _
  have : y ∈ ((cycField P₁)⟮x⟯.restrictScalars ℚ).toSubalgebra := hle (htop ▸ Algebra.mem_top)
  exact this

omit [IsScalarTower (cycField P₁) (cycField P) ℂ] in
/-- The trace of `1` is the relative degree. -/
theorem trace_one_cycField :
    Algebra.trace (cycField P₁) (cycField P) 1 =
      (finrank (cycField P₁) (cycField P) : cycField P₁) := by
  rw [← (algebraMap (cycField P₁) (cycField P)).map_one, Algebra.trace_algebraMap]
  simp

/-- Bézout for a natural number coprime to `p`: `ζ = (ζ ^ k) ^ u * (ζ ^ p) ^ v` in `ℂ`. -/
theorem zpow_bezout {ζ : ℂ} (hζ : ζ ≠ 0) {k p : ℕ} (hcop : k.Coprime p) :
    ζ = (ζ ^ k) ^ Nat.gcdA k p * (ζ ^ p) ^ Nat.gcdB k p := by
  have hexp : (k : ℤ) * Nat.gcdA k p + (p : ℤ) * Nat.gcdB k p = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
  calc ζ = ζ ^ ((k : ℤ) * Nat.gcdA k p + (p : ℤ) * Nat.gcdB k p) := by rw [hexp, zpow_one]
    _ = _ := by rw [zpow_add₀ hζ, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

/-- Reduction of an integer exponent modulo `p`. -/
theorem exists_nat_exponent {k : ℤ} {p : ℕ} (hp : 0 < p) (hk : ¬ (p : ℤ) ∣ k) :
    ∃ (k' : ℕ) (m : ℤ), 0 < k' ∧ k' < p ∧ k = (p : ℤ) * m + k' := by
  refine ⟨(k % (p : ℤ)).toNat, k / p, ?_, ?_, ?_⟩
  · have h0 : k % (p : ℤ) ≠ 0 := fun h => hk (Int.dvd_of_emod_eq_zero h)
    have h1 : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
    omega
  · have := Int.emod_lt_of_pos k (by exact_mod_cast hp : (0 : ℤ) < p)
    omega
  · have h1 : 0 ≤ k % (p : ℤ) := Int.emod_nonneg _ (by exact_mod_cast hp.ne')
    rw [Int.toNat_of_nonneg h1, add_comm]
    exact (Int.emod_add_mul_ediv k p).symm

end Generic

/-! ### Traces of powers of the generator -/

section Prime

variable {p P₁ : ℕ} (hp : p.Prime) (hP₁ : 0 < P₁)
variable [Algebra (cycField P₁) (cycField (p * P₁))]
  [IsScalarTower ℚ (cycField P₁) (cycField (p * P₁))]
  [IsScalarTower (cycField P₁) (cycField (p * P₁)) ℂ]

include hp hP₁ in
/-- **Traces of powers of `ζ_p`.** For `p ∤ P₁` and `ξ = ζ_p ∈ F_{pP₁}`, `Tr(ξ^k) = -1`
whenever `p ∤ k`. -/
theorem trace_zpow_coprime (hcop : p.Coprime P₁) (ξ : cycField (p * P₁)) (hξ : (ξ : ℂ) = zetaC p)
    (k : ℤ) (hk : ¬ (p : ℤ) ∣ k) :
    Algebra.trace (cycField P₁) (cycField (p * P₁)) (ξ ^ k) = -1 := by
  have hP : 0 < p * P₁ := Nat.mul_pos hp.pos hP₁
  have hprim : IsPrimitiveRoot ξ p := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, hξ]
    exact zetaC_isPrimitiveRoot hp.pos
  have hξne : ξ ≠ 0 := hprim.ne_zero hp.ne_zero
  obtain ⟨k', m, hk'pos, hk'lt, rfl⟩ := exists_nat_exponent hp.pos hk
  have hred : ξ ^ ((p : ℤ) * m + k') = ξ ^ k' := by
    rw [zpow_add₀ hξne, zpow_mul, zpow_natCast, hprim.pow_eq_one, one_zpow, one_mul,
      zpow_natCast]
  rw [hred]
  set x := ξ ^ k' with hx
  have hcop' : k'.Coprime p := (Nat.coprime_of_lt_prime hk'pos.ne' hk'lt hp).symm
  have hxprim : IsPrimitiveRoot x p := hprim.pow_of_coprime k' hcop'
  -- generation
  have htop : (cycField P₁)⟮x⟯ = ⊤ := by
    have hζp : zetaC p = (x : ℂ) ^ Nat.gcdA k' p := by
      have := zpow_bezout ((zetaC_isPrimitiveRoot hp.pos).ne_zero hp.ne_zero) hcop'
      rw [(zetaC_isPrimitiveRoot hp.pos).pow_eq_one, one_zpow, mul_one] at this
      rw [this, hx, IntermediateField.coe_pow, hξ]
    refine adjoin_eq_top_of_zetaC_eq hP x ⟨zetaC P₁, zetaC_mem_cycField P₁⟩
      (Nat.gcdA k' p * Nat.gcdB p P₁) (Nat.gcdA p P₁) ?_
    rw [zetaC_mul_eq_of_coprime hp.pos hP₁ hcop, hζp, zpow_mul, mul_comm]
  -- the minimal polynomial is `cyclotomic p`
  have : NeZero (p : cycField (p * P₁)) := ⟨by exact_mod_cast hp.ne_zero⟩
  have := Fact.mk hp
  have hroot : aeval x (cyclotomic p (cycField P₁)) = 0 := by
    rw [aeval_def, ← eval_map, map_cyclotomic]
    exact (isRoot_cyclotomic_iff.mpr hxprim)
  have hrank : finrank (cycField P₁) (cycField (p * P₁)) = p - 1 := by
    have h := totient_mul_finrank_cycField hP (dvd_mul_left P₁ p)
    rw [Nat.totient_mul hcop, Nat.totient_prime hp, mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.2 hP₁) h
  have hdeg : (cyclotomic p (cycField P₁)).natDegree =
      finrank (cycField P₁) (cycField (p * P₁)) := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp, hrank]
  obtain ⟨-, htr⟩ := minpoly_eq_of_adjoin_eq_top htop (cyclotomic.monic p _) hroot hdeg
  rw [htr]
  congr 1
  have hpos : 0 < (cyclotomic p (cycField P₁)).natDegree := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    omega
  rw [nextCoeff_of_natDegree_pos hpos, natDegree_cyclotomic, Nat.totient_prime hp,
    cyclotomic_prime, finsetSum_coeff]
  simp only [coeff_X_pow]
  rw [Finset.sum_ite_eq]
  have := hp.two_le
  simp [Finset.mem_range, show p - 1 - 1 < p by omega]

include hp hP₁ in
/-- **Traces of powers of `ζ_{pP₁}`.** For `p ∣ P₁` and `ξ = ζ_{pP₁}`, `Tr(ξ^k) = 0`
whenever `p ∤ k`. -/
theorem trace_zpow_dvd (hpdvd : p ∣ P₁) (ξ : cycField (p * P₁)) (hξ : (ξ : ℂ) = zetaC (p * P₁))
    (k : ℤ) (hk : ¬ (p : ℤ) ∣ k) :
    Algebra.trace (cycField P₁) (cycField (p * P₁)) (ξ ^ k) = 0 := by
  have hP : 0 < p * P₁ := Nat.mul_pos hp.pos hP₁
  have hprim : IsPrimitiveRoot ξ (p * P₁) := by
    rw [← IsPrimitiveRoot.coe_submonoidClass_iff, hξ]
    exact zetaC_isPrimitiveRoot hP
  have hξne : ξ ≠ 0 := hprim.ne_zero hP.ne'
  set η : cycField P₁ := ⟨zetaC P₁, zetaC_mem_cycField P₁⟩ with hη
  have hξp : ξ ^ p = algebraMap (cycField P₁) (cycField (p * P₁)) η := by
    apply Subtype.ext
    rw [IntermediateField.coe_pow, hξ, coe_algebraMap_cycField, zetaC_mul_pow hp.pos hP₁]
  obtain ⟨k', m, hk'pos, hk'lt, rfl⟩ := exists_nat_exponent hp.pos hk
  have hred : ξ ^ ((p : ℤ) * m + k') =
      algebraMap (cycField P₁) (cycField (p * P₁)) (η ^ m) * ξ ^ k' := by
    rw [zpow_add₀ hξne, zpow_mul, zpow_natCast, hξp, map_zpow₀, zpow_natCast]
  rw [hred, ← Algebra.smul_def, LinearMap.map_smul]
  set x := ξ ^ k' with hx
  have hcop' : k'.Coprime p := (Nat.coprime_of_lt_prime hk'pos.ne' hk'lt hp).symm
  -- generation
  have htop : (cycField P₁)⟮x⟯ = ⊤ := by
    refine adjoin_eq_top_of_zetaC_eq hP x η (Nat.gcdA k' p) (Nat.gcdB k' p) ?_
    have := zpow_bezout ((zetaC_isPrimitiveRoot hP).ne_zero hP.ne') hcop'
    rw [zetaC_mul_pow hp.pos hP₁] at this
    rw [this, hx, IntermediateField.coe_pow, hξ]
  -- the minimal polynomial is `X^p - η^k'`
  have hroot : aeval x (X ^ p - C (η ^ k')) = 0 := by
    simp only [map_sub, map_pow, aeval_X, aeval_C]
    rw [hx, ← pow_mul, mul_comm k' p, pow_mul, hξp, sub_self]
  have hrank : finrank (cycField P₁) (cycField (p * P₁)) = p := by
    have h := totient_mul_finrank_cycField hP (dvd_mul_left P₁ p)
    rw [Nat.totient_mul_of_prime_of_dvd hp hpdvd, mul_comm p P₁.totient] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.2 hP₁) h
  have hdeg : (X ^ p - C (η ^ k') : (cycField P₁)[X]).natDegree =
      finrank (cycField P₁) (cycField (p * P₁)) := by
    rw [natDegree_X_pow_sub_C, hrank]
  obtain ⟨-, htr⟩ := minpoly_eq_of_adjoin_eq_top htop (monic_X_pow_sub_C _ hp.ne_zero) hroot hdeg
  rw [htr]
  have hpos : 0 < (X ^ p - C (η ^ k') : (cycField P₁)[X]).natDegree := by
    rw [natDegree_X_pow_sub_C]; exact hp.pos
  rw [nextCoeff_of_natDegree_pos hpos, natDegree_X_pow_sub_C, coeff_sub, coeff_X_pow, coeff_C]
  have := hp.two_le
  simp [show p - 1 ≠ p by omega, show p - 1 ≠ 0 by omega]

end Prime


/-! ### Expansion of `Tr(β · conj β)` -/

section Expand

variable {P₁ P : ℕ}
variable [Algebra (cycField P₁) (cycField P)] [IsScalarTower ℚ (cycField P₁) (cycField P)]
  [IsScalarTower (cycField P₁) (cycField P) ℂ]

omit [IsScalarTower ℚ (cycField P₁) (cycField P)] in
theorem conjF_algebraMap (y : cycField P₁) :
    conjF P (algebraMap (cycField P₁) (cycField P) y) =
      algebraMap (cycField P₁) (cycField P) (conjF P₁ y) := by
  apply Subtype.ext
  rw [coe_conjF, coe_algebraMap_cycField, coe_algebraMap_cycField, coe_conjF]

omit [IsScalarTower ℚ (cycField P₁) (cycField P)] [IsScalarTower (cycField P₁) (cycField P) ℂ] in
theorem conjF_of_norm_eq_one {ξ : cycField P} (hξ : ‖(ξ : ℂ)‖ = 1) : conjF P ξ = ξ⁻¹ := by
  apply Subtype.ext
  rw [coe_conjF, IntermediateField.coe_inv, Complex.inv_eq_conj hξ]

omit [IsScalarTower ℚ (cycField P₁) (cycField P)] in
/-- `Tr_{F/F₁}(β conj β) = ∑_{i,j} a_i conj(a_j) Tr(ξ^{i-j})` for `β = ∑_j a_j ξ^j`. -/
theorem trace_mul_conjF_expand {n : ℕ} {ξ : cycField P} (hξ : ‖(ξ : ℂ)‖ = 1)
    (a : Fin n → cycField P₁) :
    Algebra.trace (cycField P₁) (cycField P)
      ((∑ j, algebraMap (cycField P₁) (cycField P) (a j) * ξ ^ (j : ℕ)) *
        conjF P (∑ j, algebraMap (cycField P₁) (cycField P) (a j) * ξ ^ (j : ℕ))) =
      ∑ i, ∑ j, a i * conjF P₁ (a j) *
        Algebra.trace (cycField P₁) (cycField P) (ξ ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) := by
  have hξne : ξ ≠ 0 := by
    intro h
    rw [h] at hξ
    simp at hξ
  rw [map_sum]
  simp only [map_mul, map_pow, conjF_algebraMap, conjF_of_norm_eq_one hξ]
  rw [Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : algebraMap (cycField P₁) (cycField P) (a i) * ξ ^ (i : ℕ) *
      (algebraMap (cycField P₁) (cycField P) (conjF P₁ (a j)) * ξ⁻¹ ^ (j : ℕ)) =
      (a i * conjF P₁ (a j)) • ξ ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) := by
    rw [Algebra.smul_def, map_mul, zpow_sub₀ hξne, zpow_natCast, zpow_natCast, inv_pow]
    ring
  rw [this, LinearMap.map_smul, smul_eq_mul]

end Expand

/-- The ring identity behind Loxton's (2.4). -/
theorem sum_sub_mul_sub_eq {R : Type*} [CommRing R] {n : ℕ} (u v : Fin n → R) :
    2 * ∑ i, ∑ j, u i * v j * ((if i = j then (n : R) else 0) - 1) =
      ∑ i, ∑ j, (u i - u j) * (v i - v j) := by
  have hL : ∑ i, ∑ j, u i * v j * ((if i = j then (n : R) else 0) - 1) =
      (n : R) * ∑ i, u i * v i - (∑ i, u i) * (∑ j, v j) := by
    have e : ∀ i j, u i * v j * ((if i = j then (n : R) else 0) - 1) =
        (if i = j then (n : R) * (u i * v i) else 0) - u i * v j := by
      intro i j
      by_cases h : i = j
      · subst h; simp; ring
      · simp [h]
    simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
  have hR : ∑ i, ∑ j, (u i - u j) * (v i - v j) =
      2 * ((n : R) * ∑ i, u i * v i) - 2 * ((∑ i, u i) * (∑ j, v j)) := by
    have e : ∀ i j, (u i - u j) * (v i - v j) =
        u i * v i + u j * v j - u i * v j - u j * v i := fun i j => by ring
    simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e1 : ∑ i : Fin n, ∑ j : Fin n, u i * v j = (∑ i, u i) * (∑ j, v j) := by
      rw [Finset.sum_mul_sum]
    have e2 : ∑ i : Fin n, ∑ j : Fin n, u j * v i = (∑ i, u i) * (∑ j, v j) := by
      rw [Finset.sum_comm, Finset.sum_mul_sum]
    have e3 : ∑ i : Fin n, (n : R) * (u i * v i) = (n : R) * ∑ i, u i * v i := by
      rw [Finset.mul_sum]
    rw [e1, e2, e3]
    ring
  rw [hL, hR]; ring

/-! ### Cassels' identities -/

section Identities

variable {p P₁ : ℕ}

theorem int_dvd_sub_fin_iff (i j : Fin p) :
    (p : ℤ) ∣ ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) ↔ i = j := by
  constructor
  · intro h
    have hi := i.2
    have hj := j.2
    have := Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; constructor <;> omega)
    exact Fin.ext (by omega)
  · rintro rfl
    simp

/-- **Loxton (2.8).** For `p ∣ P₁` and `a_j ∈ F_{P₁}`:
`M_{pP₁}(∑ a_j ζ_{pP₁}^j) = ∑ M_{P₁}(a_j)`. -/
theorem cassels_identity_dvd (hp : p.Prime) (hP₁ : 0 < P₁) (hpdvd : p ∣ P₁)
    (a : Fin p → ℂ) (ha : ∀ j, a j ∈ cycField P₁) :
    cassM (p * P₁) (∑ j, a j * zetaC (p * P₁) ^ (j : ℕ)) = ∑ j, cassM P₁ (a j) := by
  have hP : 0 < p * P₁ := Nat.mul_pos hp.pos hP₁
  have hdvd : P₁ ∣ p * P₁ := dvd_mul_left P₁ p
  let _ := towerAlgebra hP hdvd
  have := towerAlgebra_isScalarTower hP hdvd
  have := towerAlgebra_isScalarTower' hP hdvd
  set ξ : cycField (p * P₁) := ⟨zetaC (p * P₁), zetaC_mem_cycField _⟩ with hξdef
  have hξ : (ξ : ℂ) = zetaC (p * P₁) := rfl
  have hξnorm : ‖(ξ : ℂ)‖ = 1 := by rw [hξ]; exact norm_zetaC _
  let av : Fin p → cycField P₁ := fun j => ⟨a j, ha j⟩
  set βt : cycField (p * P₁) := ∑ j, algebraMap _ _ (av j) * ξ ^ (j : ℕ) with hβt
  have hβmem : (∑ j, a j * zetaC (p * P₁) ^ (j : ℕ)) ∈ cycField (p * P₁) := by
    have : (βt : ℂ) = ∑ j, a j * zetaC (p * P₁) ^ (j : ℕ) := by
      rw [hβt, IntermediateField.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [IntermediateField.coe_mul, IntermediateField.coe_pow, coe_algebraMap_cycField, hξ]
    rw [← this]; exact βt.2
  have hβeq : (⟨(∑ j, a j * zetaC (p * P₁) ^ (j : ℕ) : ℂ), hβmem⟩ : cycField (p * P₁)) = βt := by
    apply Subtype.ext
    change (∑ j, a j * zetaC (p * P₁) ^ (j : ℕ)) = (βt : ℂ)
    rw [hβt, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, coe_algebraMap_cycField, hξ]
  -- the trace values
  have htr : ∀ i j : Fin p,
      Algebra.trace (cycField P₁) (cycField (p * P₁)) (ξ ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) =
        if i = j then (p : cycField P₁) else 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, sub_self, zpow_zero, trace_one_cycField]
      have hrank : finrank (cycField P₁) (cycField (p * P₁)) = p := by
        have h := totient_mul_finrank_cycField hP hdvd
        rw [Nat.totient_mul_of_prime_of_dvd hp hpdvd, mul_comm p P₁.totient] at h
        exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.2 hP₁) h
      rw [hrank]
    · rw [ite_eq_right hij]
      exact trace_zpow_dvd hp hP₁ hpdvd ξ hξ _ (fun h => hij ((int_dvd_sub_fin_iff i j).1 h))
  have hrel : Algebra.trace (cycField P₁) (cycField (p * P₁)) (βt * conjF (p * P₁) βt) =
      (p : cycField P₁) * ∑ i, av i * conjF P₁ (av i) := by
    rw [hβt, trace_mul_conjF_expand hξnorm]
    simp only [htr, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => mul_comm _ _
  -- assemble
  have htt := Algebra.trace_trace (R := ℚ) (S := cycField P₁) (βt * conjF (p * P₁) βt)
  rw [cassM_eq_trace hP hβmem, hβeq, ← htt, hrel,
    ← nsmul_eq_mul, map_nsmul, map_sum, nsmul_eq_mul]
  have hφ : (Nat.totient (p * P₁) : ℝ) = p * Nat.totient P₁ := by
    rw [Nat.totient_mul_of_prime_of_dvd hp hpdvd]; push_cast; ring
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [hφ]
  push_cast
  rw [mul_div_mul_left _ _ hp0, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [cassM_eq_trace hP₁ (ha i)]

/-- **Loxton (2.4).** For `p ∤ P₁` and `a_j ∈ F_{P₁}`:
`2(p-1) M_{pP₁}(∑ a_j ζ_p^j) = ∑_{i,j} M_{P₁}(a_i - a_j)`. -/
theorem cassels_identity_coprime (hp : p.Prime) (hP₁ : 0 < P₁) (hndvd : ¬ p ∣ P₁)
    (a : Fin p → ℂ) (ha : ∀ j, a j ∈ cycField P₁) :
    2 * ((p : ℝ) - 1) * cassM (p * P₁) (∑ j, a j * zetaC p ^ (j : ℕ)) =
      ∑ i, ∑ j, cassM P₁ (a i - a j) := by
  have hcop : p.Coprime P₁ := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have hP : 0 < p * P₁ := Nat.mul_pos hp.pos hP₁
  have hdvd : P₁ ∣ p * P₁ := dvd_mul_left P₁ p
  let _ := towerAlgebra hP hdvd
  have := towerAlgebra_isScalarTower hP hdvd
  have := towerAlgebra_isScalarTower' hP hdvd
  have hζp : zetaC p ∈ cycField (p * P₁) := by
    rw [zetaC_dvd hP (dvd_mul_right p P₁)]
    exact pow_mem (zetaC_mem_cycField _) _
  set ξ : cycField (p * P₁) := ⟨zetaC p, hζp⟩ with hξdef
  have hξ : (ξ : ℂ) = zetaC p := rfl
  have hξnorm : ‖(ξ : ℂ)‖ = 1 := by rw [hξ]; exact norm_zetaC _
  let av : Fin p → cycField P₁ := fun j => ⟨a j, ha j⟩
  set βt : cycField (p * P₁) := ∑ j, algebraMap _ _ (av j) * ξ ^ (j : ℕ) with hβt
  have hβmem : (∑ j, a j * zetaC p ^ (j : ℕ)) ∈ cycField (p * P₁) := by
    have : (βt : ℂ) = ∑ j, a j * zetaC p ^ (j : ℕ) := by
      rw [hβt, IntermediateField.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [IntermediateField.coe_mul, IntermediateField.coe_pow, coe_algebraMap_cycField, hξ]
    rw [← this]; exact βt.2
  have hβeq : (⟨(∑ j, a j * zetaC p ^ (j : ℕ) : ℂ), hβmem⟩ : cycField (p * P₁)) = βt := by
    apply Subtype.ext
    change (∑ j, a j * zetaC p ^ (j : ℕ)) = (βt : ℂ)
    rw [hβt, IntermediateField.coe_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [IntermediateField.coe_mul, IntermediateField.coe_pow, coe_algebraMap_cycField, hξ]
  -- the trace values
  have htr : ∀ i j : Fin p,
      Algebra.trace (cycField P₁) (cycField (p * P₁)) (ξ ^ (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) =
        (if i = j then (p : cycField P₁) else 0) - 1 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [ite_eq_left rfl, sub_self, zpow_zero, trace_one_cycField]
      have hrank : finrank (cycField P₁) (cycField (p * P₁)) = p - 1 := by
        have h := totient_mul_finrank_cycField hP hdvd
        rw [Nat.totient_mul hcop, Nat.totient_prime hp, mul_comm (p - 1) P₁.totient] at h
        exact Nat.eq_of_mul_eq_mul_left (Nat.totient_pos.2 hP₁) h
      rw [hrank, Nat.cast_sub hp.one_le, Nat.cast_one]
    · rw [ite_eq_right hij, zero_sub]
      exact trace_zpow_coprime hp hP₁ hcop ξ hξ _
        (fun h => hij ((int_dvd_sub_fin_iff i j).1 h))
  have hrel : 2 * Algebra.trace (cycField P₁) (cycField (p * P₁)) (βt * conjF (p * P₁) βt) =
      ∑ i, ∑ j, (av i - av j) * conjF P₁ (av i - av j) := by
    rw [hβt, trace_mul_conjF_expand hξnorm]
    simp only [htr, map_sub]
    exact sum_sub_mul_sub_eq av (fun j => conjF P₁ (av j))
  -- assemble
  have hφ : (Nat.totient (p * P₁) : ℝ) = ((p : ℝ) - 1) * Nat.totient P₁ := by
    rw [Nat.totient_mul hcop, Nat.totient_prime hp]; push_cast [hp.one_le]; ring
  have hφ₁ : (Nat.totient P₁ : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hP₁).ne'
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    linarith
  have key : ((Algebra.trace ℚ (cycField P₁)
      (∑ i, ∑ j, (av i - av j) * conjF P₁ (av i - av j)) : ℚ) : ℝ) =
      2 * ((Algebra.trace ℚ (cycField (p * P₁)) (βt * conjF (p * P₁) βt) : ℚ) : ℝ) := by
    have h2 : ∀ z, Algebra.trace ℚ (cycField P₁) (2 * z) = 2 * Algebra.trace ℚ (cycField P₁) z :=
      fun z => by rw [two_mul, map_add, two_mul]
    have htt := Algebra.trace_trace (R := ℚ) (S := cycField P₁) (βt * conjF (p * P₁) βt)
    rw [← hrel, h2, ← htt]
    push_cast
    ring
  rw [cassM_eq_trace hP hβmem, hβeq, hφ]
  have hrhs : ∑ i, ∑ j, cassM P₁ (a i - a j) =
      ((Algebra.trace ℚ (cycField P₁)
        (∑ i, ∑ j, (av i - av j) * conjF P₁ (av i - av j)) : ℚ) : ℝ) / Nat.totient P₁ := by
    rw [map_sum]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    push_cast
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [cassM_eq_trace hP₁ (sub_mem (ha i) (ha j))]
    rfl
  rw [hrhs, key]
  field_simp

end Identities

end IngramMello
