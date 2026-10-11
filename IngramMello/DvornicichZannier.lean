import IngramMello.Loxton

/-!
# The bounded-house consequence of Dvornicich–Zannier's Theorem L, from Loxton's theorem

The bounded-house consequence, used in the proof of Lemma 4, of Theorem L of R. Dvornicich and
U. Zannier, *Cyclotomic diophantine problems (Hilbert irreducibility and invariant sets for
polynomial maps)*, Duke Math. J. 139 (2007), no. 3, 527–554, in the form `DvornicichZannier` of
`Inputs.lean`: for a number field `K ⊆ ℂ` and a house bound `B`, there are a finite set `E ⊆ K`
and an integer `N` such that every algebraic integer of `K^cyc` of house at most `B` is a sum of
at most `N` terms `c ξ` with `c ∈ E` and `ξ` a root of unity.

This is not Theorem L itself: the finite set `E` may depend on the house bound `B` (in Theorem L
it depends only on `K`), no bound on the cardinality of `E` is given, and no effective
(Loxton-function) bound on the number of terms `N` is given; only the existence of `E` and `N`
is proved.

It is deduced from Loxton's theorem (`loxton_house`) by the reduction from a number field
`K ⊆ ℂ` to `ℚ`, via the dual basis of the trace form of `K/ℚ` and the relative trace from
`L_n = F_n(K)` to the cyclotomic field `F_n = ℚ(ζ_n)`.
-/

namespace IngramMello

open IntermediateField Module

/-! ### Representations with coefficients in a finite set -/

/-- `Rep E N α`: `α` is a sum of at most `N` terms `c * ξ` with `c ∈ E` and `ξ` a root of
unity. This is the conclusion of `DvornicichZannier`. -/
def Rep (E : Finset ℂ) (N : ℕ) (α : ℂ) : Prop :=
  ∃ (n : ℕ) (c ξ : Fin n → ℂ), n ≤ N ∧ (∀ i, c i ∈ E) ∧ (∀ i, IsRootOfUnityC (ξ i)) ∧
    α = ∑ i, c i * ξ i

theorem Rep.zero (E : Finset ℂ) (N : ℕ) : Rep E N 0 :=
  ⟨0, fun i => i.elim0, fun i => i.elim0, Nat.zero_le _, fun i => i.elim0, fun i => i.elim0,
    by simp⟩

theorem Rep.mono {E : Finset ℂ} {N N' : ℕ} (h : N ≤ N') {α : ℂ} (hα : Rep E N α) :
    Rep E N' α := by
  obtain ⟨n, c, ξ, hn, hc, hξ, rfl⟩ := hα
  exact ⟨n, c, ξ, hn.trans h, hc, hξ, rfl⟩

theorem Rep.add {E : Finset ℂ} {N N' : ℕ} {α α' : ℂ} (hα : Rep E N α) (hα' : Rep E N' α') :
    Rep E (N + N') (α + α') := by
  obtain ⟨n, c, ξ, hn, hc, hξ, rfl⟩ := hα
  obtain ⟨n', c', ξ', hn', hc', hξ', rfl⟩ := hα'
  refine ⟨n + n', Fin.append c c', Fin.append ξ ξ', Nat.add_le_add hn hn', ?_, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hc j
    · rw [Fin.append_right]; exact hc' j
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hξ j
    · rw [Fin.append_right]; exact hξ' j
  · rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

theorem Rep.sum {E : Finset ℂ} {ι : Type*} (s : Finset ι) (f : ι → ℂ) (k : ι → ℕ)
    (h : ∀ i ∈ s, Rep E (k i) (f i)) : Rep E (∑ i ∈ s, k i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Rep.zero E 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact Rep.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem Rep.mul_sumRoots {E : Finset ℂ} {e : ℂ} (he : e ∈ E) {k : ℕ} {β : ℂ}
    (hβ : β ∈ SumRoots k) : Rep E k (e * β) := by
  obtain ⟨n, ξ, hn, hξ, rfl⟩ := hβ
  exact ⟨n, fun _ => e, ξ, hn, fun _ => he, hξ, by rw [Finset.mul_sum]⟩

/-! ### The dual basis of the trace form -/

section NumberField

variable (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]

/-- A fixed `ℚ`-basis of `K`. -/
noncomputable def omegaB : Basis (Fin (finrank ℚ K)) ℚ K := Module.finBasis ℚ K

/-- The dual basis of `omegaB` with respect to the trace form. -/
noncomputable def omegaD : Basis (Fin (finrank ℚ K)) ℚ K :=
  (Algebra.traceForm ℚ K).dualBasis (traceForm_nondegenerate ℚ K) (omegaB K)

/-- The basis, as complex numbers. -/
noncomputable def omegaC (j : Fin (finrank ℚ K)) : ℂ := (omegaB K j : ℂ)

theorem trace_omegaB_mul_omegaD (i j : Fin (finrank ℚ K)) :
    Algebra.trace ℚ K (omegaB K i * omegaD K j) = if i = j then 1 else 0 := by
  rw [← Algebra.traceForm_apply, omegaD,
    LinearMap.BilinForm.apply_dualBasis_right _ (Algebra.traceForm_isSymm ℚ)]

open scoped Classical in
/-- The matrix identity for the dual basis under the embeddings of `K`. -/
theorem sum_omegaD_mul_omegaB (σ σ' : K →ₐ[ℚ] ℂ) :
    ∑ j, σ (omegaD K j) * σ' (omegaB K j) = if σ = σ' then 1 else 0 := by
  classical
  let A : Matrix (Fin (finrank ℚ K)) (K →ₐ[ℚ] ℂ) ℂ := fun i τ => τ (omegaB K i)
  let B : Matrix (K →ₐ[ℚ] ℂ) (Fin (finrank ℚ K)) ℂ := fun τ j => τ (omegaD K j)
  have hAB : A * B = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    have h1 : ∑ τ : K →ₐ[ℚ] ℂ, A i τ * B τ j = ∑ τ : K →ₐ[ℚ] ℂ, τ (omegaB K i * omegaD K j) := by
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul]
    rw [h1, ← trace_eq_sum_embeddings ℂ, trace_omegaB_mul_omegaD]
    split_ifs <;> simp
  have e : (K →ₐ[ℚ] ℂ) ≃ Fin (finrank ℚ K) := Fintype.equivFinOfCardEq (AlgHom.card ℚ K ℂ)
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e.symm).1 hAB
  have := congrFun (congrFun hBA σ) σ'
  rw [Matrix.mul_apply, Matrix.one_apply] at this
  exact this

end NumberField

/-! ### The field `L = F(K)` and the trace identity -/

section Compositum

variable (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (F : IntermediateField ℚ ℂ)
  [FiniteDimensional ℚ F]

/-- `L = F(ω_1, …, ω_m)`, the compositum of `F` and `K`, as an intermediate field of `ℂ/F`. -/
noncomputable def compL : IntermediateField F ℂ :=
  IntermediateField.adjoin F (Set.range (omegaC K))

omit [FiniteDimensional ℚ F] in
theorem omegaC_mem_compL (j : Fin (finrank ℚ K)) : omegaC K j ∈ compL K F :=
  subset_adjoin F _ (Set.mem_range_self j)

theorem isIntegral_omegaC (j : Fin (finrank ℚ K)) : IsIntegral ℚ (omegaC K j) :=
  (IsIntegral.of_finite ℚ (omegaB K j)).map K.val

instance compL_finiteDimensional : FiniteDimensional F (compL K F) := by
  have : Finite (Set.range (omegaC K)) := (Set.finite_range _).to_subtype
  exact IntermediateField.finiteDimensional_adjoin fun x hx => by
    obtain ⟨j, rfl⟩ := hx
    exact (isIntegral_omegaC K j).tower_top

instance compL_finiteDimensional_rat : FiniteDimensional ℚ (compL K F) :=
  FiniteDimensional.trans ℚ F (compL K F)

example : IsScalarTower ℚ F (compL K F) := inferInstance
example : IsScalarTower F (compL K F) ℂ := inferInstance
example : Algebra.IsSeparable F (compL K F) := inferInstance

omit [FiniteDimensional ℚ F] in
/-- Elements of `K` lie in `L`. -/
theorem coe_mem_compL (x : K) : (x : ℂ) ∈ compL K F := by
  have hx : (x : ℂ) = ∑ i, ((omegaB K).repr x i : ℚ) • omegaC K i := by
    conv_lhs => rw [← (omegaB K).sum_repr x]
    rw [IntermediateField.coe_sum]
    rfl
  rw [hx]
  refine sum_mem fun i _ => ?_
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply ℚ F ℂ]
  exact mul_mem (IntermediateField.algebraMap_mem _ _) (omegaC_mem_compL K F i)

/-- The inclusion `K → L` as a `ℚ`-algebra map. -/
noncomputable def inclK : K →ₐ[ℚ] compL K F where
  toFun x := ⟨x, coe_mem_compL K F x⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' q := Subtype.ext (by simp)

omit [FiniteDimensional ℚ F] in
@[simp] theorem coe_inclK (x : K) : ((inclK K F x : compL K F) : ℂ) = x := rfl

/-- The canonical embedding `L → ℂ` as an `F`-algebra map. -/
noncomputable abbrev tauZero : compL K F →ₐ[F] ℂ := IsScalarTower.toAlgHom F (compL K F) ℂ

omit [FiniteDimensional ℚ F] in
@[simp] theorem tauZero_apply (y : compL K F) : tauZero K F y = (y : ℂ) := rfl

/-- Restriction of an `F`-embedding of `L` to `K`. -/
noncomputable def resK {E : Type*} [Field E] [Algebra ℚ E] [Algebra F E] [IsScalarTower ℚ F E]
    (τ : compL K F →ₐ[F] E) : K →ₐ[ℚ] E :=
  (τ.restrictScalars ℚ).comp (inclK K F)

omit [FiniteDimensional ℚ F] in
theorem resK_apply {E : Type*} [Field E] [Algebra ℚ E] [Algebra F E] [IsScalarTower ℚ F E]
    (τ : compL K F →ₐ[F] E) (x : K) : resK K F τ x = τ (inclK K F x) := rfl

omit [FiniteDimensional ℚ F] in
/-- Two `F`-embeddings of `L` agreeing on `K` are equal. -/
theorem algHom_ext_of_resK {E : Type*} [Field E] [Algebra ℚ E] [Algebra F E]
    [IsScalarTower ℚ F E] {τ τ' : compL K F →ₐ[F] E} (h : resK K F τ = resK K F τ') :
    τ = τ' := by
  refine IntermediateField.adjoin_algHom_ext F ?_
  rintro x ⟨j, rfl⟩
  change τ (inclK K F (omegaB K j)) = τ' (inclK K F (omegaB K j))
  rw [← resK_apply, ← resK_apply, h]

omit [FiniteDimensional ℚ F] in
theorem resK_injective {E : Type*} [Field E] [Algebra ℚ E] [Algebra F E]
    [IsScalarTower ℚ F E] : Function.Injective (resK K F (E := E)) :=
  fun _ _ h => algHom_ext_of_resK K F h

omit [FiniteDimensional ℚ F] in
theorem resK_tauZero : resK K F (tauZero K F) = K.val := by
  ext x
  rfl

omit [FiniteDimensional ℚ F] in
/-- The trace identity: `y = ∑_j Tr_{L/F}(y ω*_j) ω_j`. -/
theorem sum_trace_mul_omegaC (y : compL K F) :
    ∑ j, (algebraMap F ℂ (Algebra.trace F (compL K F) (y * inclK K F (omegaD K j)))) *
      omegaC K j = (y : ℂ) := by
  classical
  simp_rw [trace_eq_sum_embeddings ℂ (K := F) (L := compL K F), Finset.sum_mul, map_mul]
  rw [Finset.sum_comm]
  have key : ∀ τ : compL K F →ₐ[F] ℂ,
      ∑ j, τ y * τ (inclK K F (omegaD K j)) * omegaC K j =
        τ y * (if τ = tauZero K F then 1 else 0) := by
    intro τ
    have h1 : ∑ j, τ y * τ (inclK K F (omegaD K j)) * omegaC K j =
        τ y * ∑ j, resK K F τ (omegaD K j) * K.val (omegaB K j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [resK_apply, mul_assoc]
      rfl
    rw [h1, sum_omegaD_mul_omegaB]
    congr 1
    by_cases hτ : τ = tauZero K F
    · rw [ite_eq_left hτ, ite_eq_left]
      rw [hτ, resK_tauZero]
    · rw [ite_eq_right hτ, ite_eq_right]
      intro h
      exact hτ (algHom_ext_of_resK K F (h.trans (resK_tauZero K F).symm))
  simp_rw [key, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (tauZero K F)]
  simp

end Compositum

/-! ### House bound and integrality of relative traces -/

/-- `ℂ` as an `F`-algebra through an embedding `ρ : F → ℂ` (a type synonym, so that this
structure does not clash with the inclusion `F ⊆ ℂ`). -/
def Twist (F : IntermediateField ℚ ℂ) (_ρ : F →ₐ[ℚ] ℂ) : Type := ℂ

namespace Twist

variable {F : IntermediateField ℚ ℂ} (ρ : F →ₐ[ℚ] ℂ)

noncomputable instance : Field (Twist F ρ) := inferInstanceAs (Field ℂ)
noncomputable instance : Algebra ℚ (Twist F ρ) := inferInstanceAs (Algebra ℚ ℂ)
instance : IsAlgClosed (Twist F ρ) := inferInstanceAs (IsAlgClosed ℂ)
noncomputable instance algebraF : Algebra F (Twist F ρ) := ρ.toRingHom.toAlgebra
instance : @IsScalarTower ℚ F (Twist F ρ) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
  IsScalarTower.of_algebraMap_eq fun q => (ρ.commutes q).symm

theorem algebraMap_apply (x : F) : algebraMap F (Twist F ρ) x = ρ x := rfl

/-- The identity `Twist F ρ → ℂ`, as a `ℚ`-algebra map. -/
noncomputable def toC : Twist F ρ →ₐ[ℚ] ℂ := AlgHom.id ℚ ℂ

theorem toC_apply (x : Twist F ρ) : toC ρ x = x := rfl

end Twist

section TraceBounds

variable (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] (F : IntermediateField ℚ ℂ)
  [FiniteDimensional ℚ F]

/-- Every conjugate of `Tr_{L/F}(z)` is bounded by `[K:ℚ]` times the house of `z`. -/
theorem norm_algHom_trace_le (z : compL K F) {M : ℝ} (hz : HouseLE (z : ℂ) M)
    (ρ : F →ₐ[ℚ] ℂ) :
    ‖ρ (Algebra.trace F (compL K F) z)‖ ≤ finrank ℚ K * M := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hz _ (minpoly.aeval ℚ _))
  have hz' : HouseLE (((compL K F).val.restrictScalars ℚ) z) M := hz
  have h := trace_eq_sum_embeddings (Twist F ρ) (K := F) (L := compL K F) (x := z)
  rw [Twist.algebraMap_apply] at h
  have h' : ρ (Algebra.trace F (compL K F) z) =
      ∑ τ : compL K F →ₐ[F] Twist F ρ, Twist.toC ρ (τ z) := by
    rw [← map_sum, ← h]
    rfl
  have hcard : Fintype.card (compL K F →ₐ[F] Twist F ρ) ≤ finrank ℚ K := by
    rw [← AlgHom.card ℚ K ℂ]
    exact Fintype.card_le_of_injective _ (resK_injective K F (E := Twist F ρ))
  have hbound : ∀ τ : compL K F →ₐ[F] Twist F ρ, ‖Twist.toC ρ (τ z)‖ ≤ M := fun τ =>
    (houseLE_iff_embeddings ((compL K F).val.restrictScalars ℚ) z M).1 hz'
      ((Twist.toC ρ).comp (τ.restrictScalars ℚ))
  calc ‖ρ (Algebra.trace F (compL K F) z)‖
      = ‖∑ τ : compL K F →ₐ[F] Twist F ρ, Twist.toC ρ (τ z)‖ := by rw [h']
    _ ≤ ∑ τ : compL K F →ₐ[F] Twist F ρ, ‖Twist.toC ρ (τ z)‖ := norm_sum_le _ _
    _ ≤ ∑ _τ : compL K F →ₐ[F] Twist F ρ, M := Finset.sum_le_sum fun τ _ => hbound τ
    _ = Fintype.card (compL K F →ₐ[F] Twist F ρ) * M := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ finrank ℚ K * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM

omit [FiniteDimensional ℚ F] in
/-- The relative trace of an algebraic integer is an algebraic integer. -/
theorem isIntegral_trace_compL (z : compL K F) (hz : IsIntegral ℤ (z : ℂ)) :
    IsIntegral ℤ ((Algebra.trace F (compL K F) z : F) : ℂ) := by
  have hz' : IsIntegral ℤ z :=
    (isIntegral_algHom_iff ((compL K F).val.restrictScalars ℚ).toRingHom.toIntAlgHom
      Subtype.val_injective).1 hz
  exact (Algebra.isIntegral_trace (R := ℤ) (L := F) hz').map F.val.toRingHom.toIntAlgHom

end TraceBounds

/-! ### Finite conductor -/

section Conductor

variable (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]

/-- Every element of `K^cyc` lies in `L_n = F_n(K)` for some conductor `n ≥ 1`. -/
theorem exists_conductor {α : ℂ} (hα : α ∈ Kcyc K) :
    ∃ n : ℕ, 0 < n ∧ α ∈ compL K (cycField n) := by
  classical
  have hα' : α ∈ IntermediateField.adjoin ℚ ((K : Set ℂ) ∪ {ζ : ℂ | IsRootOfUnityC ζ}) := by
    refine (sup_le ?_ ?_ : Kcyc K ≤ _) hα
    · exact fun x hx => subset_adjoin ℚ _ (Or.inl hx)
    · exact IntermediateField.adjoin.mono ℚ _ _ Set.subset_union_right
  obtain ⟨T, hT, hαT⟩ := exists_finset_of_mem_adjoin hα'
  have hk : ∀ t : ℂ, ∃ k : ℕ, 0 < k ∧ (IsRootOfUnityC t → t ^ k = 1) := by
    intro t
    by_cases h : IsRootOfUnityC t
    · obtain ⟨k, hk, hpow⟩ := h
      exact ⟨k, hk, fun _ => hpow⟩
    · exact ⟨1, one_pos, fun h' => absurd h' h⟩
  choose k hkpos hkpow using hk
  set n := ∏ t ∈ T, k t with hn_def
  have hn : 0 < n := Finset.prod_pos fun t _ => hkpos t
  have : NeZero n := ⟨hn.ne'⟩
  have hroot : ∀ t ∈ T, IsRootOfUnityC t → t ∈ cycField n := by
    intro t ht hμ
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem k ht
    have htn : t ^ n = 1 := by
      rw [hn_def, hc, pow_mul, hkpow t hμ, one_pow]
    obtain ⟨i, -, hi⟩ := (zetaC_isPrimitiveRoot hn).eq_pow_of_pow_eq_one htn
    rw [← hi]
    exact pow_mem (zetaC_mem_cycField n) i
  have hle : IntermediateField.adjoin ℚ (T : Set ℂ) ≤
      (compL K (cycField n)).restrictScalars ℚ := by
    rw [IntermediateField.adjoin_le_iff]
    intro t ht
    rw [SetLike.mem_coe, IntermediateField.mem_restrictScalars]
    rcases hT ht with htK | htμ
    · exact coe_mem_compL K (cycField n) ⟨t, htK⟩
    · have := (compL K (cycField n)).algebraMap_mem ⟨t, hroot t ht htμ⟩
      simpa using this
  refine ⟨n, hn, ?_⟩
  have := hle hαT
  rwa [IntermediateField.mem_restrictScalars] at this

end Conductor

/-! ### The theorem -/

/-- **The bounded-house consequence of Dvornicich–Zannier's Theorem L** used in the proof of
Lemma 4, in the form `DvornicichZannier` of `Inputs.lean`, deduced from Loxton's theorem
(`loxton_house`). This is not Theorem L itself: the finite set `E` may depend on the house bound
`B`, no bound on the cardinality of `E` is given, and no effective (Loxton-function) bound on
the number of terms `N` is given; only the existence of `E` and `N` is proved. -/
theorem dvornicichZannier_of_loxton : DvornicichZannier := by
  classical
  intro K hK B
  -- the denominator `D`
  have hex : ∀ j : Fin (finrank ℚ K), ∃ y : ℤ, y ≠ 0 ∧ IsIntegral ℤ (y • (omegaD K j : ℂ)) := by
    intro j
    exact ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).2
      (isAlgebraic_iff_isIntegral.2 ((IsIntegral.of_finite ℚ (omegaD K j)).map K.val))
      ).exists_integral_multiple
  choose y hy0 hyint using hex
  set D : ℕ := ∏ j, (y j).natAbs with hD_def
  have hD : 0 < D := Finset.prod_pos fun j _ => Int.natAbs_pos.2 (hy0 j)
  have hDint : ∀ j, IsIntegral ℤ ((D : ℂ) * omegaD K j) := by
    intro j
    have hy' : IsIntegral ℤ ((y j : ℂ) * omegaD K j) := by
      have := hyint j
      rwa [zsmul_eq_mul] at this
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun j => (y j).natAbs) (Finset.mem_univ j)
    have hD' : (D : ℂ) = ((y j).natAbs : ℂ) * c := by
      rw [hD_def, hc]; push_cast; ring
    have habs : IsIntegral ℤ (((y j).natAbs : ℂ) * omegaD K j) := by
      rw [Nat.cast_natAbs]
      rcases abs_choice (y j) with h | h <;> rw [h]
      · exact hy'
      · push_cast
        rw [neg_mul]
        exact hy'.neg
    rw [hD', mul_comm _ (c : ℂ), mul_assoc]
    exact (isIntegral_natCast c).mul habs
  -- the house bound `C`
  set C : ℝ := ∑ j, ∑ σ : K →ₐ[ℚ] ℂ, ‖σ ((D : K) * omegaD K j)‖ with hC_def
  have hC : ∀ j, HouseLE ((D : ℂ) * omegaD K j) C := by
    intro j
    have : ((D : ℂ) * (omegaD K j : ℂ)) = K.val ((D : K) * omegaD K j) := by simp
    rw [this]
    refine (houseLE_iff_embeddings K.val _ C).2 fun σ => ?_
    calc ‖σ ((D : K) * omegaD K j)‖
        ≤ ∑ σ : K →ₐ[ℚ] ℂ, ‖σ ((D : K) * omegaD K j)‖ :=
          Finset.single_le_sum (f := fun σ : K →ₐ[ℚ] ℂ => ‖σ ((D : K) * omegaD K j)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ σ)
      _ ≤ C := Finset.single_le_sum (f := fun j => ∑ σ : K →ₐ[ℚ] ℂ, ‖σ ((D : K) * omegaD K j)‖)
          (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
  -- Loxton's constant
  obtain ⟨Λ, hΛ⟩ := loxton_house (finrank ℚ K * (B * C))
  refine ⟨Finset.univ.image (fun j => omegaC K j / D), ?_, finrank ℚ K * Λ, ?_⟩
  · intro e he
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 he
    exact div_mem (omegaB K j).2 (IntermediateField.natCast_mem K D)
  intro α hα hαint hαB
  obtain ⟨n, hn, hαL⟩ := exists_conductor K hα
  set F := cycField n with hF
  set α' : compL K F := ⟨α, hαL⟩ with hα'
  obtain ⟨z, hz⟩ : ∃ z : Fin (finrank ℚ K) → compL K F,
      z = fun j => α' * inclK K F ((D : K) * omegaD K j) := ⟨_, rfl⟩
  have hzcoe : ∀ j, ((z j : compL K F) : ℂ) = α * ((D : ℂ) * omegaD K j) := by
    intro j
    rw [hz]
    simp only [IntermediateField.coe_mul, coe_inclK]
    rw [hα']
    push_cast
    rfl
  set β : Fin (finrank ℚ K) → F := fun j => Algebra.trace F (compL K F) (z j) with hβ
  have hβint : ∀ j, IsIntegral ℤ ((β j : F) : ℂ) := fun j =>
    isIntegral_trace_compL K F (z j) (by rw [hzcoe]; exact hαint.mul (hDint j))
  have hβhouse : ∀ j, HouseLE ((β j : F) : ℂ) (finrank ℚ K * (B * C)) := by
    intro j
    refine (houseLE_iff_embeddings F.val (β j) _).2 fun ρ => ?_
    apply norm_algHom_trace_le K F (z j) _ ρ
    rw [hzcoe]
    exact HouseLE.mul hαB (hC j) hαint.tower_top (hDint j).tower_top
  have hβsum : ∀ j, ((β j : F) : ℂ) ∈ SumRoots Λ := fun j =>
    hΛ n hn _ (β j).2 (hβint j) (hβhouse j)
  -- the identity `α = ∑ (ω_j / D) β_j`
  have hβeq : ∀ j, ((β j : F) : ℂ) =
      (D : ℂ) * algebraMap F ℂ (Algebra.trace F (compL K F) (α' * inclK K F (omegaD K j))) := by
    intro j
    have h1 : z j = (D : F) • (α' * inclK K F (omegaD K j)) := by
      rw [hz]
      simp only
      rw [map_mul, map_natCast, Algebra.smul_def, map_natCast]
      ring
    simp only [hβ]
    rw [h1, LinearMap.map_smul, smul_eq_mul]
    push_cast
    rfl
  have hαeq : α = ∑ j, omegaC K j / D * (β j : ℂ) := by
    have hD' : (D : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
    have := sum_trace_mul_omegaC K F α'
    have hcoe : (α' : ℂ) = α := rfl
    rw [hcoe] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hβeq j]
    field_simp
  have hrep : Rep (Finset.univ.image (fun j => omegaC K j / D))
      (∑ _j : Fin (finrank ℚ K), Λ) α := by
    rw [hαeq]
    exact Rep.sum _ _ _ fun j _ =>
      Rep.mul_sumRoots (Finset.mem_image_of_mem _ (Finset.mem_univ j)) (hβsum j)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hrep
  exact hrep

end IngramMello
