import IngramMello.LaurentOrder

/-!
# Torsion points and monomial maps

A monomial map `w ↦ η · w^B` from `(ℂ^×)^s` to `(ℂ^×)^r` with `B.mulVec` injective (rank `s`,
as in the parametrizations of torsion cosets produced by `Laurent`) has finite kernel.
Consequently, when `η` is torsion, the preimage of a torsion point consists of torsion
points (`isOfFinOrder_of_monomialMap`). This is what makes the finite-kernel
parametrizations of `Laurent` usable in the descent of Lemma 9 in place of isomorphisms.

The key identity is `adj(BᵀB) Bᵀ B = det(BᵀB) · 1` with `det(BᵀB) ≠ 0`.
-/

namespace IngramMello

namespace MvLaurent

variable {r s : ℕ}

/-- Composition of monomial maps: `(w^B)^C = w^{C B}`. -/
theorem monomialMap_one_comp {t : ℕ} (B : Matrix (Fin r) (Fin s) ℤ)
    (C : Matrix (Fin t) (Fin r) ℤ) (w : Fin s → ℂˣ) :
    monomialMap 1 C (monomialMap 1 B w) = monomialMap 1 (C * B) w := by
  funext i
  have h := prod_monomialMap_zpow 1 B w (C i)
  simp only [Pi.one_apply, one_zpow, Finset.prod_const_one, one_mul] at h
  simp only [monomialMap, Pi.one_apply, one_mul] at h ⊢
  rw [h]
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]

/-- If `B.mulVec` is injective then `det(BᵀB) ≠ 0`. -/
theorem det_transpose_mul_ne_zero (B : Matrix (Fin r) (Fin s) ℤ)
    (hB : Function.Injective B.mulVec) : (B.transpose * B).det ≠ 0 := by
  intro h
  obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h
  apply hv
  apply hB
  rw [Matrix.mulVec_zero]
  have : (B.mulVec v) ⬝ᵥ (B.mulVec v) = 0 :=
    calc (B.mulVec v) ⬝ᵥ (B.mulVec v) = (Matrix.vecMul v B.transpose) ⬝ᵥ (B.mulVec v) := by
          rw [Matrix.vecMul_transpose]
      _ = v ⬝ᵥ (B.transpose.mulVec (B.mulVec v)) := (Matrix.dotProduct_mulVec ..).symm
      _ = 0 := by rw [Matrix.mulVec_mulVec, hGv, dotProduct_zero]
  exact dotProduct_self_eq_zero.1 this

/-- `B` has a left inverse up to a nonzero integer: `C B = N · 1`. -/
theorem exists_left_inverse_smul (B : Matrix (Fin r) (Fin s) ℤ)
    (hB : Function.Injective B.mulVec) :
    ∃ (C : Matrix (Fin s) (Fin r) ℤ) (N : ℤ), N ≠ 0 ∧ C * B = N • (1 : Matrix (Fin s) (Fin s) ℤ) :=
  ⟨(B.transpose * B).adjugate * B.transpose, (B.transpose * B).det,
    det_transpose_mul_ne_zero B hB, by rw [Matrix.mul_assoc, Matrix.adjugate_mul]⟩

theorem monomialMap_one_smul_one (N : ℤ) (w : Fin s → ℂˣ) (k : Fin s) :
    monomialMap 1 (N • (1 : Matrix (Fin s) (Fin s) ℤ)) w k = w k ^ N := by
  simp only [monomialMap, Pi.one_apply, one_mul, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.prod_eq_single k (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
  simp

theorem isOfFinOrder_of_zpow {G : Type*} [Group G] {g : G} {N : ℤ} (hN : N ≠ 0)
    (h : IsOfFinOrder (g ^ N)) : IsOfFinOrder g := by
  have h2 : IsOfFinOrder (g ^ ((N.natAbs * N.natAbs : ℕ) : ℤ)) := by
    rw [Int.natAbs_mul_self, zpow_mul]
    exact h.zpow
  rw [zpow_natCast, isOfFinOrder_pow] at h2
  exact h2.resolve_right (by simpa using hN)

/-- **Preimages of torsion are torsion.** Let `B.mulVec` be injective and `η` torsion. If
`η · w^B` is a torsion point of `(ℂ^×)^r`, then `w` is a torsion point of `(ℂ^×)^s`. -/
theorem isOfFinOrder_of_monomialMap (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (hB : Function.Injective B.mulVec) (hη : ∀ j, IsOfFinOrder (η j)) (w : Fin s → ℂˣ)
    (hw : ∀ j, IsOfFinOrder (monomialMap η B w j)) (k : Fin s) : IsOfFinOrder (w k) := by
  obtain ⟨C, N, hN, hCB⟩ := exists_left_inverse_smul B hB
  have h1 : ∀ j, IsOfFinOrder (monomialMap 1 B w j) := fun j => by
    have : monomialMap 1 B w j = (η j)⁻¹ * monomialMap η B w j := by
      simp [monomialMap]
    rw [this]
    exact (hη j).inv.mul (hw j)
  have h2 : IsOfFinOrder (monomialMap 1 C (monomialMap 1 B w) k) := by
    have hC : ∀ y : Fin r → ℂˣ, monomialMap 1 C y k = ∏ j, y j ^ C k j := fun y => by
      simp [monomialMap]
    rw [hC, ← CommGroup.mem_torsion]
    exact Subgroup.prod_mem _ fun j _ => (CommGroup.mem_torsion _).2 (h1 j).zpow
  rw [monomialMap_one_comp, hCB, monomialMap_one_smul_one] at h2
  exact isOfFinOrder_of_zpow hN h2

/-- `IsRootOfUnityC` is torsion in `ℂˣ`. -/
theorem isRootOfUnityC_iff_isOfFinOrder (u : ℂˣ) : IsRootOfUnityC (u : ℂ) ↔ IsOfFinOrder u := by
  rw [isOfFinOrder_iff_pow_eq_one, IsRootOfUnityC]
  refine exists_congr fun n => and_congr_right fun _ => ?_
  rw [← Units.val_pow_eq_pow_val, Units.val_eq_one]

end MvLaurent

section Density
open AddMonoidAlgebra

/-- Evaluate a Laurent polynomial at a point with nonzero coordinates via `evalHom`. -/
theorem MvLaurent.eval_eq_evalHom {r : ℕ} (P : MvLaurent r) (u : Fin r → ℂ) (hu : ∀ j, u j ≠ 0) :
    MvLaurent.eval P u = MvLaurent.evalHom (fun j => Units.mk0 (u j) (hu j)) P := by
  rw [MvLaurent.evalHom_apply]
  rfl

theorem cosetPt_ne_zero {r s : ℕ} {η : Fin r → ℂ} (hη : ∀ j, η j ≠ 0)
    (B : Matrix (Fin r) (Fin s) ℤ) {w : Fin s → ℂ} (hw : ∀ k, w k ≠ 0) (j : Fin r) :
    cosetPt η B w j ≠ 0 :=
  mul_ne_zero (hη j) (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw k))

/-- A nonzero integer power map on `ℂ^×` is surjective. -/
theorem exists_zpow_eq {m : ℤ} (hm : m ≠ 0) {c : ℂ} (hc : c ≠ 0) : ∃ t : ℂ, t ≠ 0 ∧ t ^ m = c := by
  rcases Int.natAbs_eq m with h | h
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c (Int.natAbs_pos.2 hm)
    refine ⟨t, fun h0 => hc ?_, ?_⟩
    · rw [← ht, h0, zero_pow (Int.natAbs_pos.2 hm).ne']
    · rw [h, zpow_natCast, ht]
  · obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq c⁻¹ (Int.natAbs_pos.2 hm)
    refine ⟨t, fun h0 => hc ?_, ?_⟩
    · rw [← inv_inv c, ← ht, h0, zero_pow (Int.natAbs_pos.2 hm).ne', inv_zero]
    · rw [h, zpow_neg, zpow_natCast, ht, inv_inv]

/-- The points of a torsion coset, as a set. -/
def cosetSet {r s : ℕ} (η : Fin r → ℂ) (B : Matrix (Fin r) (Fin s) ℤ) : Set (Fin r → ℂ) :=
  {p | ∃ w : Fin s → ℂ, (∀ k, w k ≠ 0) ∧ cosetPt η B w = p}

/-- **Zariski-dense subsets of positive-dimensional cosets are infinite.** In the
conclusion of `Laurent`, `T ∩ C` is infinite. -/
theorem infinite_of_laurent_dense {r s : ℕ} (hs : 0 < s) {η : Fin r → ℂ} (hη : ∀ j, η j ≠ 0)
    {B : Matrix (Fin r) (Fin s) ℤ} (hB : Function.Injective B.mulVec) (T : Set (Fin r → ℂ))
    (hdense : ∀ P : MvLaurent r,
        (∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → cosetPt η B w ∈ T →
          MvLaurent.eval P (cosetPt η B w) = 0) →
        ∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → MvLaurent.eval P (cosetPt η B w) = 0) :
    (T ∩ cosetSet η B).Infinite := by
  classical
  intro hfin
  let k₀ : Fin s := ⟨0, hs⟩
  obtain ⟨j, hj⟩ : ∃ j, B j k₀ ≠ 0 := by
    by_contra h
    push Not at h
    have : B.mulVec (Pi.single k₀ 1) = B.mulVec 0 := by
      funext j
      simp [h j]
    exact one_ne_zero (congrFun (hB this) k₀ |>.symm.trans (by simp) |>.symm)
  let F := hfin.toFinset
  let P : MvLaurent r := ∏ p ∈ F, (single (Pi.single j 1) 1 - single 0 (p j))
  have hP : ∀ u : Fin r → ℂ, (hu : ∀ i, u i ≠ 0) →
      MvLaurent.eval P u = ∏ p ∈ F, (u j - p j) := by
    intro u hu
    rw [MvLaurent.eval_eq_evalHom P u hu, map_prod]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [map_sub, MvLaurent.evalHom_single, MvLaurent.evalHom_single]
    simp [Pi.single_apply]
  have hvan := hdense P fun w hw hT => by
    rw [hP _ (cosetPt_ne_zero hη B hw)]
    exact Finset.prod_eq_zero (hfin.mem_toFinset.2 ⟨hT, w, hw, rfl⟩) (sub_self _)
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset (insert (0 : ℂ) (F.image fun p => p j))
  have hz0 : z ≠ 0 := fun h => hz (h ▸ Finset.mem_insert_self _ _)
  obtain ⟨t, ht0, ht⟩ := exists_zpow_eq hj (div_ne_zero hz0 (hη j))
  let w : Fin s → ℂ := Function.update (fun _ => 1) k₀ t
  have hw : ∀ k, w k ≠ 0 := fun k => by
    by_cases hk : k = k₀
    · subst hk; simp [w, ht0]
    · simp [w, hk]
  have hcj : cosetPt η B w j = z := by
    simp only [cosetPt]
    rw [Finset.prod_eq_single k₀ (fun k _ hk => by simp [w, hk]) (by simp)]
    simp [w, ht, mul_div_cancel₀ _ (hη j)]
  have := hvan w hw
  rw [hP _ (cosetPt_ne_zero hη B hw), Finset.prod_eq_zero_iff] at this
  obtain ⟨p, hp, hpz⟩ := this
  rw [hcj, sub_eq_zero] at hpz
  exact hz (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨p, hp, hpz.symm⟩))

end Density

end IngramMello
