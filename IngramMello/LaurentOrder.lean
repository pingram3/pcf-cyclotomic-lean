import IngramMello.Inputs

/-!
# Orders of vanishing of Laurent polynomials

Infrastructure for `MvLaurent r = ℂ[u₁^{±1}, …, u_r^{±1}]`.

* `MvLaurent.evalHom x` is evaluation at a point `x ∈ (ℂ^×)^r`, as a `ℂ`-algebra map.
  It agrees with `MvLaurent.eval` from `Inputs.lean` (`MvLaurent.evalHom_apply`).
* `MvLaurent.maxIdeal x` is its kernel, the maximal ideal `𝔪_x` of `x`. We say
  `ord_x F ≥ n` when `F ∈ 𝔪_x ^ n`. This matches the paper, which defines `ord_x` on
  `K[V]` via powers of the maximal ideal `𝔪_x ⊆ K[V]` of functions vanishing at `x`
  (rather than in the local ring); for the varieties used here the two agree, since
  `𝔪_x ^ n` is `𝔪_x`-primary.
* `MvLaurent.eulerD w` is the Euler derivation `u^a ↦ w(a) u^a` attached to an additive
  weight `w : ℤ^r → ℂ`. Any such derivation lowers the order by at most one
  (`MvLaurent.eulerD_mem_pow`).
-/

namespace IngramMello

open AddMonoidAlgebra

namespace MvLaurent

variable {r : ℕ}

/-- The character `a ↦ x^a = ∏ⱼ xⱼ^{aⱼ}` of `ℤ^r` attached to `x ∈ (ℂ^×)^r`. -/
noncomputable def character (x : Fin r → ℂˣ) : Multiplicative (Fin r → ℤ) →* ℂ :=
  (Units.coeHom ℂ).comp
    { toFun := fun a => ∏ j, x j ^ (Multiplicative.toAdd a j)
      map_one' := by simp
      map_mul' := fun a b => by
        simp [zpow_add, Finset.prod_mul_distrib] }

/-- Evaluation at `x ∈ (ℂ^×)^r` as a `ℂ`-algebra homomorphism. -/
noncomputable def evalHom (x : Fin r → ℂˣ) : MvLaurent r →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin r → ℤ) (character x)

theorem evalHom_single (x : Fin r → ℂˣ) (a : Fin r → ℤ) (β : ℂ) :
    evalHom x (single a β) = β * ∏ j, ((x j : ℂ) ^ a j) := by
  simp [evalHom, character, Units.val_zpow_eq_zpow_val]

/-- `evalHom` agrees with `MvLaurent.eval` of `Inputs.lean`. -/
theorem evalHom_apply (x : Fin r → ℂˣ) (F : MvLaurent r) :
    evalHom x F = MvLaurent.eval F (fun j => (x j : ℂ)) := by
  simp [evalHom, AddMonoidAlgebra.lift_apply', MvLaurent.eval, character,
    Units.val_zpow_eq_zpow_val]

/-- The maximal ideal `𝔪_x` of the point `x ∈ (ℂ^×)^r`. -/
noncomputable def maxIdeal (x : Fin r → ℂˣ) : Ideal (MvLaurent r) :=
  RingHom.ker (evalHom x)

theorem mem_maxIdeal {x : Fin r → ℂˣ} {F : MvLaurent r} :
    F ∈ maxIdeal x ↔ evalHom x F = 0 :=
  RingHom.mem_ker

/-- A monomial `β u^a` with `β ≠ 0` does not vanish at any point of `(ℂ^×)^r`. -/
theorem single_notMem_maxIdeal (x : Fin r → ℂˣ) (a : Fin r → ℤ) {β : ℂ} (hβ : β ≠ 0) :
    single a β ∉ maxIdeal x := by
  rw [mem_maxIdeal, evalHom_single]
  exact mul_ne_zero hβ (Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (x j).ne_zero)

/-! ### Euler derivations -/

/-- The Euler derivation `∑ β_a u^a ↦ ∑ w(a) β_a u^a` for an additive weight `w`. For
`w(a) = a · s` this is `∑ⱼ sⱼ uⱼ ∂/∂uⱼ`. -/
noncomputable def eulerD (w : (Fin r → ℤ) →+ ℂ) : MvLaurent r →ₗ[ℂ] MvLaurent r where
  toFun F := ofCoeff (Finsupp.onFinset F.coeff.support (fun a => w a * F.coeff a)
    (fun a h => Finsupp.mem_support_iff.2 (right_ne_zero_of_mul h)))
  map_add' F G := by
    ext a
    simp [mul_add]
  map_smul' c F := by
    ext a
    simp only [Finsupp.onFinset_apply, coeff_smul, Finsupp.smul_apply,
      smul_eq_mul, RingHom.id_apply]
    ring

@[simp]
theorem coeff_eulerD (w : (Fin r → ℤ) →+ ℂ) (F : MvLaurent r) (a : Fin r → ℤ) :
    (eulerD w F).coeff a = w a * F.coeff a := by
  simp [eulerD]

theorem eulerD_single (w : (Fin r → ℤ) →+ ℂ) (a : Fin r → ℤ) (β : ℂ) :
    eulerD w (single a β) = single a (w a * β) := by
  ext b
  simp only [coeff_eulerD, coeff_single, Finsupp.single_apply]
  split_ifs with h
  · rw [h]
  · simp

/-- The Leibniz rule for `eulerD`. -/
theorem eulerD_mul (w : (Fin r → ℤ) →+ ℂ) (F G : MvLaurent r) :
    eulerD w (F * G) = F * eulerD w G + G * eulerD w F := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add F₁ F₂ h₁ h₂ =>
    rw [add_mul, map_add, h₁, h₂, map_add]
    ring
  | single a α =>
    induction G using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add G₁ G₂ h₁ h₂ =>
      rw [mul_add, map_add, h₁, h₂, map_add]
      ring
    | single b β =>
      simp only [eulerD_single, single_mul_single, map_add, add_comm b a, ← single_add]
      congr 1
      ring

/-- An Euler derivation lowers the order of vanishing along any ideal by at most one. -/
theorem eulerD_mem_pow (w : (Fin r → ℤ) →+ ℂ) (I : Ideal (MvLaurent r)) :
    ∀ (n : ℕ) (F : MvLaurent r), F ∈ I ^ (n + 1) → eulerD w F ∈ I ^ n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
    intro F hF
    rw [pow_succ] at hF
    refine Submodule.mul_induction_on hF (fun G hG H hH => ?_) (fun G H hG hH => ?_)
    · rw [eulerD_mul]
      refine add_mem (Ideal.mul_mem_right _ _ hG) ?_
      rw [pow_succ']
      exact Ideal.mul_mem_mul hH (ih G hG)
    · rw [map_add]
      exact add_mem hG hH

/-! ### Pullback along monomial maps -/

/-- The point `η · w^B ∈ (ℂ^×)^r` with coordinates `ηⱼ ∏ₖ wₖ^{Bⱼₖ}`, for `w ∈ (ℂ^×)^s`.
Its coercion to `ℂ^r` is `cosetPt η B w` (`coe_monomialMap`). -/
def monomialMap {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ) (w : Fin s → ℂˣ) :
    Fin r → ℂˣ :=
  fun j => η j * ∏ k, w k ^ B j k

theorem coe_monomialMap {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (w : Fin s → ℂˣ) :
    (fun j => (monomialMap η B w j : ℂ)) = cosetPt (fun j => (η j : ℂ)) B (fun k => w k) := by
  funext j
  simp [monomialMap, cosetPt, Units.val_zpow_eq_zpow_val]

/-- Pullback `φ^*` along `φ(w) = η · w^B`: `u^a ↦ η^a w^{Bᵀ a}`. -/
noncomputable def pullback {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ) :
    MvLaurent r →ₐ[ℂ] MvLaurent s :=
  AddMonoidAlgebra.lift ℂ (MvLaurent s) (Fin r → ℤ)
    { toFun := fun a => single (B.transpose.mulVec (Multiplicative.toAdd a)) (character η a)
      map_one' := by simp [one_def]
      map_mul' := fun a b => by simp [Matrix.mulVec_add] }

theorem pullback_single {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (a : Fin r → ℤ) (β : ℂ) :
    pullback η B (single a β) =
      single (B.transpose.mulVec a) (β * ∏ j, ((η j : ℂ) ^ a j)) := by
  simp [pullback, character, Units.val_zpow_eq_zpow_val]

theorem zpow_finset_sum {G ι : Type*} [CommGroup G] (g : G) (t : Finset ι) (n : ι → ℤ) :
    g ^ (∑ i ∈ t, n i) = ∏ i ∈ t, g ^ n i := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.prod_insert hi, zpow_add, ih]

/-- Monomial identity behind `evalHom_pullback`: `(η w^B)^a = η^a w^{Bᵀ a}`. -/
theorem prod_monomialMap_zpow {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (w : Fin s → ℂˣ) (a : Fin r → ℤ) :
    ∏ j, monomialMap η B w j ^ a j =
      (∏ j, η j ^ a j) * ∏ k, w k ^ (B.transpose.mulVec a) k := by
  simp only [monomialMap, mul_zpow, Finset.prod_mul_distrib, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, zpow_finset_sum, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]

/-- Evaluation commutes with pullback: `(φ^* F)(w) = F(φ(w))`. -/
theorem evalHom_pullback {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (w : Fin s → ℂˣ) (F : MvLaurent r) :
    evalHom w (pullback η B F) = evalHom (monomialMap η B w) F := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add F G hF hG => simp [hF, hG]
  | single a β =>
    rw [pullback_single, evalHom_single, evalHom_single, mul_assoc]
    congr 1
    have := congrArg (fun u : ℂˣ => (u : ℂ)) (prod_monomialMap_zpow η B w a)
    simpa [Units.val_zpow_eq_zpow_val] using this.symm

theorem maxIdeal_le_comap_pullback {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (w : Fin s → ℂˣ) :
    maxIdeal (monomialMap η B w) ≤ (maxIdeal w).comap (pullback η B) := fun F hF => by
  rw [Ideal.mem_comap, mem_maxIdeal, evalHom_pullback]
  exact mem_maxIdeal.1 hF

/-- **Order under pullback** (the order inequality `ord_{φ(x)} F ≤ ord_x φ^*F` of the paper), for
monomial maps:
`ord_{φ(w)} F ≤ ord_w (φ^* F)`. -/
theorem pullback_mem_pow {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (w : Fin s → ℂˣ) {n : ℕ} {F : MvLaurent r} (hF : F ∈ maxIdeal (monomialMap η B w) ^ n) :
    pullback η B F ∈ maxIdeal w ^ n := by
  have h1 : pullback η B F ∈ (maxIdeal (monomialMap η B w) ^ n).map (pullback η B) :=
    Ideal.mem_map_of_mem _ hF
  rw [Ideal.map_pow] at h1
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 (maxIdeal_le_comap_pullback η B w)) n h1

theorem coeff_pullback_mulVec {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (hB : Function.Injective B.transpose.mulVec) (F : MvLaurent r) (b : Fin r → ℤ) :
    (pullback η B F).coeff (B.transpose.mulVec b) = F.coeff b * ∏ j, ((η j : ℂ) ^ b j) := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add F G hF hG => simp [hF, hG, add_mul]
  | single a β =>
    rw [pullback_single, coeff_single, coeff_single, Finsupp.single_apply, Finsupp.single_apply]
    simp only [hB.eq_iff]
    split_ifs with h
    · rw [h]
    · simp

/-- Pullback along `φ(w) = η w^B` is injective when `Bᵀ : ℤ^r → ℤ^s` is injective (for
instance when `φ` is dominant). -/
theorem pullback_injective {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (hB : Function.Injective B.transpose.mulVec) : Function.Injective (pullback η B) := by
  rw [injective_iff_map_eq_zero]
  intro F hF
  ext b
  have h := coeff_pullback_mulVec η B hB F b
  rw [hF, coeff_zero, Finsupp.zero_apply, eq_comm] at h
  rcases mul_eq_zero.1 h with h | h
  · simpa using h
  · exact absurd h (Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ (η j).ne_zero)

/-! ### Surjectivity of monomial maps -/

/-- `ℂˣ` is divisible, so (as a `ℤ`-module) injective. -/
noncomputable instance : DivisibleBy (Additive ℂˣ) ℤ :=
  divisibleByOfSMulRightSurj _ _ fun {n} hn y => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (y.toMul : ℂ) (Int.natAbs_pos.2 hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow (Int.natAbs_pos.2 hn).ne'] at hz
      exact y.toMul.ne_zero hz.symm
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
      apply Additive.toMul.injective
      ext
      simp only [toMul_zsmul, toMul_ofMul, Units.val_zpow_eq_zpow_val, Units.val_mk0]
      rw [h, zpow_natCast, hz]
    · refine ⟨Additive.ofMul (Units.mk0 z hz0)⁻¹, ?_⟩
      apply Additive.toMul.injective
      ext
      simp only [toMul_zsmul, toMul_ofMul, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val,
        Units.val_mk0]
      rw [h, zpow_neg, inv_zpow, inv_inv, zpow_natCast, hz]

/-- **Monomial maps of full rank are surjective.** If `Bᵀ : ℤ^r → ℤ^s` is injective, every
point of `(ℂ^×)^r` is `η · w^B` for some `w ∈ (ℂ^×)^s`. -/
theorem exists_monomialMap_eq {s : ℕ} (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (hB : Function.Injective B.transpose.mulVec) (x : Fin r → ℂˣ) :
    ∃ w : Fin s → ℂˣ, monomialMap η B w = x := by
  classical
  let y : Fin r → ℂˣ := fun j => (η j)⁻¹ * x j
  let g : (Fin r → ℤ) →+ Additive ℂˣ :=
    { toFun := fun a => Additive.ofMul (∏ j, y j ^ a j)
      map_zero' := by simp
      map_add' := fun a b => by
        simp [zpow_add, Finset.prod_mul_distrib] }
  let f : (Fin r → ℤ) →+ (Fin s → ℤ) := B.transpose.mulVecLin.toAddMonoidHom
  obtain ⟨h, hh⟩ := (Module.Baer.of_divisible (Additive ℂˣ)).extension_property_addMonoidHom
    f hB g
  refine ⟨fun k => (h (Pi.single k 1)).toMul, funext fun j => ?_⟩
  have hv : ∀ v : Fin s → ℤ, (h v).toMul = ∏ k, (h (Pi.single k 1)).toMul ^ v k := by
    intro v
    conv_lhs => rw [← Finset.univ_sum_single v]
    simp only [map_sum, toMul_sum]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [← toMul_zsmul, ← map_zsmul]
    congr 2
    rw [← Pi.single_smul, smul_eq_mul, mul_one]
  have hj := congrArg (fun φ : (Fin r → ℤ) →+ Additive ℂˣ => (φ (Pi.single j 1)).toMul) hh
  simp only [AddMonoidHom.coe_comp, Function.comp_apply] at hj
  rw [hv] at hj
  have hf : ∀ k, f (Pi.single j 1) k = B j k := fun k => by
    simp [f]
  simp only [hf] at hj
  have hg : (g (Pi.single j 1)).toMul = y j := by
    change ∏ i, y i ^ (Pi.single j (1 : ℤ) : Fin r → ℤ) i = y j
    rw [Finset.prod_eq_single j (fun i _ hi => by rw [Pi.single_eq_of_ne hi, zpow_zero])
      (by simp), Pi.single_eq_same, zpow_one]
  rw [monomialMap, hj, hg, mul_inv_cancel_left]

end MvLaurent

end IngramMello
