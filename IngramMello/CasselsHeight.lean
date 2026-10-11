import IngramMello.Descent
import IngramMello.Mann

/-!
# Cassels' mean-square height on cyclotomic fields

Infrastructure for the proofs of Loxton's theorem and of `DvornicichZannier`: the cyclotomic
field `F_P = ℚ(ζ_P) ⊆ ℂ`, the ring `R_P = ℤ[ζ_P]`, sums of at most `k` roots of unity, and
Cassels' height `M_P(β) = (1/φ(P)) ∑_σ ‖σ β‖²` (mean of `|β'|²` over the conjugates `β'` of
`β`), introduced in J. W. S. Cassels, *On a conjecture of R. M. Robinson about sums of roots of
unity*, J. Reine Angew. Math. 238 (1969), 112–131, and used by Loxton.
-/

namespace IngramMello

open Polynomial IntermediateField

/-! ### The cyclotomic field `F_P` and the ring `R_P` -/

/-- `ζ_P = exp(2πi/P)`. -/
noncomputable def zetaC (P : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / P)

theorem zetaC_isPrimitiveRoot {P : ℕ} (hP : 0 < P) : IsPrimitiveRoot (zetaC P) P :=
  Complex.isPrimitiveRoot_exp P hP.ne'

/-- The cyclotomic field `F_P = ℚ(ζ_P)` inside `ℂ`. -/
noncomputable abbrev cycField (P : ℕ) : IntermediateField ℚ ℂ := ℚ⟮zetaC P⟯

/-- The ring `R_P = ℤ[ζ_P]` inside `ℂ`. -/
noncomputable def cycInt (P : ℕ) : Subalgebra ℤ ℂ := Algebra.adjoin ℤ {zetaC P}

theorem zetaC_mem_cycField (P : ℕ) : zetaC P ∈ cycField P :=
  IntermediateField.mem_adjoin_simple_self ℚ (zetaC P)

theorem zetaC_isIntegral {P : ℕ} (hP : 0 < P) : IsIntegral ℚ (zetaC P) :=
  ((zetaC_isPrimitiveRoot hP).isIntegral hP).tower_top

theorem zetaC_isIntegral_int {P : ℕ} (hP : 0 < P) : IsIntegral ℤ (zetaC P) :=
  (zetaC_isPrimitiveRoot hP).isIntegral hP

instance cycField_finiteDimensional (P : ℕ) : FiniteDimensional ℚ (cycField P) := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · have : zetaC 0 = 1 := by simp [zetaC]
    unfold cycField
    rw [this]
    exact IntermediateField.adjoin.finiteDimensional isIntegral_one
  · exact IntermediateField.adjoin.finiteDimensional (zetaC_isIntegral hP)

theorem cycField_finrank {P : ℕ} (hP : 0 < P) :
    Module.finrank ℚ (cycField P) = Nat.totient P := by
  unfold cycField
  rw [IntermediateField.adjoin.finrank (zetaC_isIntegral hP),
    ← cyclotomic_eq_minpoly_rat (zetaC_isPrimitiveRoot hP) hP, natDegree_cyclotomic]

theorem mem_cycField_of_mem_cycInt {P : ℕ} {β : ℂ} (hβ : β ∈ cycInt P) : β ∈ cycField P := by
  unfold cycInt at hβ
  refine Algebra.adjoin_induction (hx := hβ) ?_ ?_ ?_ ?_
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact zetaC_mem_cycField P
  · intro r
    exact (cycField P).intCast_mem r
  · intro x y _ _ hx hy
    exact (cycField P).add_mem hx hy
  · intro x y _ _ hx hy
    exact (cycField P).mul_mem hx hy

theorem isIntegral_of_mem_cycInt {P : ℕ} (hP : 0 < P) {β : ℂ} (hβ : β ∈ cycInt P) :
    IsIntegral ℤ β := by
  unfold cycInt at hβ
  have : Algebra.adjoin ℤ {zetaC P} ≤ integralClosure ℤ ℂ := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact zetaC_isIntegral_int hP
  exact this hβ

/-- Powers of `ζ_P` (integer exponents) lie in `R_P`. -/
theorem zetaC_zpow_mem_cycInt {P : ℕ} (hP : 0 < P) (k : ℤ) : zetaC P ^ k ∈ cycInt P := by
  have hζ := zetaC_isPrimitiveRoot hP
  have hne : zetaC P ≠ 0 := hζ.ne_zero hP.ne'
  have : zetaC P ^ k = zetaC P ^ (k % (P : ℤ)).toNat := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k P]
    rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow, mul_one,
      ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hP.ne'))]
  rw [this]
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _

theorem zetaC_pow_mem_cycInt {P : ℕ} (k : ℕ) : zetaC P ^ k ∈ cycInt P :=
  Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _

/-- `ζ_{P₁} = ζ_P ^ (P / P₁)` for `P₁ ∣ P`. -/
theorem zetaC_dvd {P₁ P : ℕ} (hP : 0 < P) (h : P₁ ∣ P) : zetaC P₁ = zetaC P ^ (P / P₁) := by
  obtain ⟨m, rfl⟩ := h
  have hP₁ : 0 < P₁ := Nat.pos_of_mul_pos_right hP
  have hm : 0 < m := Nat.pos_of_mul_pos_left hP
  rw [Nat.mul_div_cancel_left _ hP₁]
  unfold zetaC
  rw [← Complex.exp_nat_mul]
  congr 1
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have hP₁' : (P₁ : ℂ) ≠ 0 := by exact_mod_cast hP₁.ne'
  push_cast
  field_simp

theorem cycInt_mono {P₁ P : ℕ} (hP : 0 < P) (h : P₁ ∣ P) : cycInt P₁ ≤ cycInt P := by
  unfold cycInt
  rw [Algebra.adjoin_le_iff]
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  rw [hx, zetaC_dvd hP h]
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) _

theorem cycField_mono {P₁ P : ℕ} (hP : 0 < P) (h : P₁ ∣ P) : cycField P₁ ≤ cycField P := by
  unfold cycField
  rw [IntermediateField.adjoin_simple_le_iff, zetaC_dvd hP h]
  exact pow_mem (zetaC_mem_cycField P) _

/-! ### Sums of at most `k` roots of unity -/

/-- `SumRoots k` is the set of sums of at most `k` roots of unity. -/
def SumRoots (k : ℕ) : Set ℂ :=
  {β | ∃ (n : ℕ) (ξ : Fin n → ℂ), n ≤ k ∧ (∀ i, IsRootOfUnityC (ξ i)) ∧ β = ∑ i, ξ i}

theorem SumRoots.zero_mem (k : ℕ) : (0 : ℂ) ∈ SumRoots k :=
  ⟨0, fun i => i.elim0, Nat.zero_le _, fun i => i.elim0, by simp⟩

theorem SumRoots.mono {k l : ℕ} (h : k ≤ l) : SumRoots k ⊆ SumRoots l := by
  rintro β ⟨n, ξ, hn, hξ, rfl⟩
  exact ⟨n, ξ, hn.trans h, hξ, rfl⟩

theorem SumRoots.root_mem {ρ : ℂ} (hρ : IsRootOfUnityC ρ) : ρ ∈ SumRoots 1 :=
  ⟨1, fun _ => ρ, le_rfl, fun _ => hρ, by simp⟩

theorem SumRoots.add {k l : ℕ} {β γ : ℂ} (hβ : β ∈ SumRoots k) (hγ : γ ∈ SumRoots l) :
    β + γ ∈ SumRoots (k + l) := by
  obtain ⟨n, ξ, hn, hξ, rfl⟩ := hβ
  obtain ⟨m, η, hm, hη, rfl⟩ := hγ
  refine ⟨n + m, Fin.append ξ η, Nat.add_le_add hn hm, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]; exact hξ j
    · rw [Fin.append_right]; exact hη j
  · rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]

theorem SumRoots.mul_root {k : ℕ} {ρ β : ℂ} (hρ : IsRootOfUnityC ρ) (hβ : β ∈ SumRoots k) :
    ρ * β ∈ SumRoots k := by
  obtain ⟨n, ξ, hn, hξ, rfl⟩ := hβ
  exact ⟨n, fun i => ρ * ξ i, hn, fun i => hρ.mul (hξ i), by rw [Finset.mul_sum]⟩

theorem SumRoots.neg {k : ℕ} {β : ℂ} (hβ : β ∈ SumRoots k) : -β ∈ SumRoots k := by
  have h : IsRootOfUnityC (-1 : ℂ) := ⟨2, by norm_num, by norm_num⟩
  simpa using SumRoots.mul_root h hβ

theorem SumRoots.sum {ι : Type*} (s : Finset ι) (f : ι → ℂ) (k : ι → ℕ)
    (h : ∀ i ∈ s, f i ∈ SumRoots (k i)) : ∑ i ∈ s, f i ∈ SumRoots (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using SumRoots.zero_mem 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact SumRoots.add (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem SumRoots.natCast {k : ℕ} (n : ℕ) (hn : n ≤ k) : ((n : ℕ) : ℂ) ∈ SumRoots k :=
  ⟨n, fun _ => 1, hn, fun _ => ⟨1, one_pos, one_pow 1⟩, by simp⟩

theorem SumRoots.intCast {k : ℕ} (m : ℤ) (hm : m.natAbs ≤ k) : ((m : ℤ) : ℂ) ∈ SumRoots k := by
  rcases Int.natAbs_eq m with h | h
  · rw [h, Int.cast_natCast]; exact SumRoots.natCast m.natAbs hm
  · rw [h, Int.cast_neg, Int.cast_natCast]
    exact SumRoots.neg (SumRoots.natCast m.natAbs hm)

/-! ### Complex conjugation on `F_P` -/

theorem norm_zetaC (P : ℕ) : ‖zetaC P‖ = 1 := by
  rcases Nat.eq_zero_or_pos P with rfl | hP
  · simp [zetaC]
  · exact (zetaC_isPrimitiveRoot hP).norm'_eq_one hP.ne'

/-- Complex conjugation as a `ℚ`-algebra map. -/
noncomputable def conjQ : ℂ →ₐ[ℚ] ℂ := (Complex.conjAe.restrictScalars ℚ).toAlgHom

@[simp] theorem conjQ_apply (z : ℂ) : conjQ z = starRingEnd ℂ z := rfl

theorem conj_mem_cycField {P : ℕ} {β : ℂ} (hβ : β ∈ cycField P) :
    starRingEnd ℂ β ∈ cycField P := by
  have h : cycField P ≤ (cycField P).comap conjQ := by
    unfold cycField
    rw [IntermediateField.adjoin_simple_le_iff]
    change conjQ (zetaC P) ∈ cycField P
    rw [conjQ_apply, ← Complex.inv_eq_conj (norm_zetaC P)]
    exact inv_mem (zetaC_mem_cycField P)
  exact h hβ

/-- Complex conjugation restricted to `F_P`. -/
noncomputable def conjF (P : ℕ) : cycField P →ₐ[ℚ] cycField P where
  toFun x := ⟨starRingEnd ℂ x, conj_mem_cycField x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  commutes' q := Subtype.ext (by simp)

@[simp] theorem coe_conjF {P : ℕ} (x : cycField P) : (conjF P x : ℂ) = starRingEnd ℂ x := rfl

/-- Every embedding of `F_P` commutes with complex conjugation. -/
theorem algHom_conjF {P : ℕ} (hP : 0 < P) (σ : cycField P →ₐ[ℚ] ℂ) (x : cycField P) :
    σ (conjF P x) = starRingEnd ℂ (σ x) := by
  have key : σ.comp (conjF P) = conjQ.comp σ := by
    apply (IntermediateField.adjoin.powerBasis (zetaC_isIntegral hP)).algHom_ext
    rw [IntermediateField.adjoin.powerBasis_gen]
    simp only [AlgHom.comp_apply, conjQ_apply]
    have hgen : (conjF P (IntermediateField.AdjoinSimple.gen ℚ (zetaC P))) =
        (IntermediateField.AdjoinSimple.gen ℚ (zetaC P))⁻¹ := by
      apply Subtype.ext
      rw [coe_conjF, IntermediateField.coe_inv, IntermediateField.AdjoinSimple.coe_gen,
        Complex.inv_eq_conj (norm_zetaC P)]
    rw [hgen, map_inv₀]
    apply Complex.inv_eq_conj
    have h1 : (σ (IntermediateField.AdjoinSimple.gen ℚ (zetaC P))) ^ P = 1 := by
      rw [← map_pow]
      have : (IntermediateField.AdjoinSimple.gen ℚ (zetaC P)) ^ P = 1 := by
        apply Subtype.ext
        simp [(zetaC_isPrimitiveRoot hP).pow_eq_one]
      rw [this, map_one]
    have h2 : ‖σ (IntermediateField.AdjoinSimple.gen ℚ (zetaC P))‖ ^ P = 1 := by
      rw [← norm_pow, h1, norm_one]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hP.ne').1 h2
  exact congrArg (fun f => f x) key

/-! ### Cassels' height `M_P` -/

open scoped Classical in
/-- Cassels' height `M_P(β) = (1/φ(P)) ∑_σ ‖σ β‖²` for `β ∈ F_P` (and `0` otherwise). -/
noncomputable def cassM (P : ℕ) (β : ℂ) : ℝ :=
  if h : β ∈ cycField P then
    (∑ σ : cycField P →ₐ[ℚ] ℂ, ‖σ ⟨β, h⟩‖ ^ 2) / Nat.totient P
  else 0

theorem cassM_of_mem {P : ℕ} {β : ℂ} (h : β ∈ cycField P) :
    cassM P β = (∑ σ : cycField P →ₐ[ℚ] ℂ, ‖σ ⟨β, h⟩‖ ^ 2) / Nat.totient P := by
  simp [cassM, h]

theorem cassM_nonneg (P : ℕ) (β : ℂ) : 0 ≤ cassM P β := by
  by_cases h : β ∈ cycField P
  · rw [cassM_of_mem h]
    exact div_nonneg (Finset.sum_nonneg fun _ _ => by positivity) (Nat.cast_nonneg _)
  · simp [cassM, h]

theorem cassM_zero (P : ℕ) : cassM P 0 = 0 := by
  rw [cassM_of_mem (zero_mem _)]
  have : (⟨0, zero_mem _⟩ : cycField P) = 0 := rfl
  simp [this]

theorem cassM_neg (P : ℕ) (β : ℂ) : cassM P (-β) = cassM P β := by
  by_cases h : β ∈ cycField P
  · rw [cassM_of_mem h, cassM_of_mem (neg_mem h)]
    congr 1
    refine Finset.sum_congr rfl fun σ _ => ?_
    have : (⟨-β, neg_mem h⟩ : cycField P) = -⟨β, h⟩ := rfl
    rw [this, map_neg, norm_neg]
  · have h' : -β ∉ cycField P := fun h' => h (by simpa using neg_mem h')
    simp [cassM, h, h']

/-- The house bounds Cassels' height. -/
theorem cassM_le_sq_of_houseLE {P : ℕ} (hP : 0 < P) {β : ℂ} (hβ : β ∈ cycField P) {B : ℝ}
    (h : HouseLE β B) : cassM P β ≤ B ^ 2 := by
  rw [cassM_of_mem hβ]
  have hφ : (0 : ℝ) < Nat.totient P := by exact_mod_cast Nat.totient_pos.2 hP
  rw [div_le_iff₀ hφ]
  have hemb : ∀ σ : cycField P →ₐ[ℚ] ℂ, ‖σ ⟨β, hβ⟩‖ ≤ B :=
    (houseLE_iff_embeddings (cycField P).val ⟨β, hβ⟩ B).1 (by simpa using h)
  calc (∑ σ : cycField P →ₐ[ℚ] ℂ, ‖σ ⟨β, hβ⟩‖ ^ 2)
      ≤ ∑ _σ : cycField P →ₐ[ℚ] ℂ, B ^ 2 :=
        Finset.sum_le_sum fun σ _ => pow_le_pow_left₀ (norm_nonneg _) (hemb σ) 2
    _ = B ^ 2 * Nat.totient P := by
        rw [Finset.sum_const, Finset.card_univ, AlgHom.card, cycField_finrank hP,
          nsmul_eq_mul, mul_comm]

/-- A nonzero algebraic integer in `F_P` has Cassels height at least `1`
(AM–GM applied to the conjugates, whose product is the norm, a nonzero rational integer). -/
theorem one_le_cassM {P : ℕ} (hP : 0 < P) {β : ℂ} (hβ : β ∈ cycField P)
    (hint : IsIntegral ℤ β) (hne : β ≠ 0) : 1 ≤ cassM P β := by
  rw [cassM_of_mem hβ]
  set x : cycField P := ⟨β, hβ⟩ with hx
  have hφ : (0 : ℝ) < Nat.totient P := by exact_mod_cast Nat.totient_pos.2 hP
  have hcard : (Fintype.card (cycField P →ₐ[ℚ] ℂ) : ℝ) = Nat.totient P := by
    rw [AlgHom.card, cycField_finrank hP]
  have hxint : IsIntegral ℤ x :=
    (isIntegral_algHom_iff ((cycField P).val.restrictScalars ℤ) Subtype.val_injective).1 hint
  have hnint : IsIntegral ℤ (Algebra.norm ℚ x) := Algebra.isIntegral_norm ℚ hxint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hnint
  have hxne : x ≠ 0 := fun h => hne (congrArg Subtype.val h)
  have hyne : y ≠ 0 := by
    rintro rfl
    exact hxne (by simpa using hy.symm)
  have hprod : ∏ σ : cycField P →ₐ[ℚ] ℂ, ‖σ x‖ ^ 2 = ((y : ℤ) : ℝ) ^ 2 := by
    rw [Finset.prod_pow, ← norm_prod, ← Algebra.norm_eq_prod_embeddings ℚ ℂ x, ← hy]
    simp
  have hprod1 : 1 ≤ ∏ σ : cycField P →ₐ[ℚ] ℂ, ‖σ x‖ ^ 2 := by
    rw [hprod]
    have : (1 : ℝ) ≤ |(y : ℝ)| := by exact_mod_cast Int.one_le_abs hyne
    nlinarith [sq_abs (y : ℝ)]
  have hw : ∑ _σ : cycField P →ₐ[ℚ] ℂ, 1 / (Nat.totient P : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
    field_simp
  have hamgm := Real.geom_mean_le_arith_mean_weighted Finset.univ
    (fun _ => 1 / (Nat.totient P : ℝ)) (fun σ : cycField P →ₐ[ℚ] ℂ => ‖σ x‖ ^ 2)
    (fun _ _ => by positivity) hw (fun _ _ => by positivity)
  rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)] at hamgm
  have hge : (1 : ℝ) ≤ (∏ σ : cycField P →ₐ[ℚ] ℂ, ‖σ x‖ ^ 2) ^ (1 / (Nat.totient P : ℝ)) :=
    Real.one_le_rpow hprod1 (by positivity)
  calc (1 : ℝ) ≤ _ := hge
    _ ≤ ∑ σ : cycField P →ₐ[ℚ] ℂ, 1 / (Nat.totient P : ℝ) * ‖σ x‖ ^ 2 := hamgm
    _ = (∑ σ : cycField P →ₐ[ℚ] ℂ, ‖σ x‖ ^ 2) / Nat.totient P := by
        rw [← Finset.mul_sum]; ring

/-- The bridge between the embedding sum and the trace of `x · conj x`. -/
theorem trace_mul_conjF {P : ℕ} (hP : 0 < P) (x : cycField P) :
    algebraMap ℚ ℂ (Algebra.trace ℚ (cycField P) (x * conjF P x)) =
      ((∑ σ : cycField P →ₐ[ℚ] ℂ, ‖σ x‖ ^ 2 : ℝ) : ℂ) := by
  rw [trace_eq_sum_embeddings ℂ]
  push_cast
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, algHom_conjF hP, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- Cassels' height as a trace. -/
theorem cassM_eq_trace {P : ℕ} (hP : 0 < P) {β : ℂ} (hβ : β ∈ cycField P) :
    cassM P β =
      ((Algebra.trace ℚ (cycField P) (⟨β, hβ⟩ * conjF P ⟨β, hβ⟩) : ℚ) : ℝ) / Nat.totient P := by
  rw [cassM_of_mem hβ]
  congr 1
  have h := trace_mul_conjF hP ⟨β, hβ⟩
  rw [eq_ratCast, ← Complex.ofReal_ratCast] at h
  exact (Complex.ofReal_injective h).symm

/-- `M_P(m) = m²` for an integer `m`. -/
theorem cassM_intCast {P : ℕ} (hP : 0 < P) (m : ℤ) : cassM P (m : ℂ) = (m : ℝ) ^ 2 := by
  have hm : (m : ℂ) ∈ cycField P := intCast_mem _ m
  rw [cassM_of_mem hm]
  have hφ : (Nat.totient P : ℝ) ≠ 0 := by exact_mod_cast (Nat.totient_pos.2 hP).ne'
  have hx : (⟨(m : ℂ), hm⟩ : cycField P) = (m : cycField P) := Subtype.ext (by simp)
  rw [hx]
  simp only [map_intCast, Complex.norm_intCast, sq_abs, Finset.sum_const, Finset.card_univ,
    AlgHom.card, cycField_finrank hP, nsmul_eq_mul]
  field_simp

/-! ### The base level `P = 1` -/

theorem zetaC_one : zetaC 1 = 1 := by
  simp [zetaC, Complex.exp_two_pi_mul_I]

theorem mem_cycInt_one_iff {β : ℂ} : β ∈ cycInt 1 ↔ ∃ m : ℤ, β = m := by
  unfold cycInt
  rw [zetaC_one, Algebra.adjoin_singleton_one, Algebra.mem_bot]
  constructor
  · rintro ⟨m, rfl⟩; exact ⟨m, by simp⟩
  · rintro ⟨m, rfl⟩; exact ⟨m, by simp⟩

/-- At level `1`: `β ∈ R_1` lies in `S_k` for some `k ≤ M_1(β)`. -/
theorem exists_mem_sumRoots_of_mem_cycInt_one {β : ℂ} (hβ : β ∈ cycInt 1) :
    ∃ k : ℕ, (k : ℝ) ≤ cassM 1 β ∧ β ∈ SumRoots k := by
  obtain ⟨m, rfl⟩ := mem_cycInt_one_iff.1 hβ
  refine ⟨m.natAbs, ?_, SumRoots.intCast m le_rfl⟩
  rw [cassM_intCast one_pos]
  have h1 : ((m.natAbs : ℕ) : ℝ) = |(m : ℝ)| := by rw [Nat.cast_natAbs, Int.cast_abs]
  rw [h1]
  have : (|(m : ℝ)|) ^ 2 = (m : ℝ) ^ 2 := sq_abs _
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  · have h2 : (1 : ℝ) ≤ |(m : ℝ)| := by exact_mod_cast Int.one_le_abs hm
    nlinarith

end IngramMello
