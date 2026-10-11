import IngramMello.LaurentOrder

/-!
# Lemma 6 for `r > 1`: restriction to a monomial curve

The cited `SuperAttracting` covers one-parameter families over `ℂ[t^{±1}]`. The paper reduces
`r > 1` to this by pulling back along a monomial curve `t ↦ t^β` for a generic `β ∈ ℤ^r`.

* `MvLaurent.curve β`: the pullback `ℂ[u^{±1}] → ℂ[t^{±1}]`, `u^a ↦ t^{β·a}`.
* `MvLaurent.eval₂_curve`: evaluation at `t₀` is evaluation at `t₀^β`.
* `MvLaurent.eq_zero_of_forall_evalHom`: a Laurent polynomial vanishing on `(ℂ^×)^r` is 0.
* `MvLaurent.exists_curve_not_const`: some `β` keeps finitely many non-constant Laurent
  polynomials non-constant (Kronecker substitution `βᵢ = Nⁱ`).
-/

namespace IngramMello
open AddMonoidAlgebra

namespace MvLaurent
variable {r : ℕ}

/-- Restriction to the monomial curve `t ↦ (t^{β₁}, …, t^{β_r})`: `u^a ↦ t^{β·a}`. -/
noncomputable def curve (β : Fin r → ℤ) : MvLaurent r →ₐ[ℂ] LaurentPolynomial ℂ :=
  AddMonoidAlgebra.lift ℂ (LaurentPolynomial ℂ) (Fin r → ℤ)
    { toFun := fun a => LaurentPolynomial.T (β ⬝ᵥ Multiplicative.toAdd a)
      map_one' := by simp
      map_mul' := fun a b => by simp only [toAdd_mul, dotProduct_add, LaurentPolynomial.T_add] }

theorem curve_single (β : Fin r → ℤ) (a : Fin r → ℤ) (c : ℂ) :
    curve β (single a c) = LaurentPolynomial.C c * LaurentPolynomial.T (β ⬝ᵥ a) := by
  simp [curve, Algebra.smul_def]

theorem curve_single' (β : Fin r → ℤ) (a : Fin r → ℤ) (c : ℂ) :
    curve β (single a c) = (single (β ⬝ᵥ a) c : LaurentPolynomial ℂ) := by
  rw [curve_single, LaurentPolynomial.single_eq_C_mul_T]

/-- Evaluating the restriction at `t₀` is evaluating at `(t₀^{β₁}, …, t₀^{β_r})`. -/
theorem eval₂_curve (β : Fin r → ℤ) (t₀ : ℂˣ) (F : MvLaurent r) :
    LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀ (curve β F) =
      evalHom (fun j => t₀ ^ β j) F := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add F G hF hG => simp [hF, hG]
  | single a c =>
    rw [curve_single, LaurentPolynomial.eval₂_C_mul_T, evalHom_single, RingHom.id_apply]
    congr 1
    have : t₀ ^ (β ⬝ᵥ a) = ∏ j, (t₀ ^ β j) ^ a j := by
      simp only [dotProduct, zpow_finset_sum, ← zpow_mul]
    rw [this]
    simp [Units.val_zpow_eq_zpow_val]

theorem coeff_curve (β : Fin r → ℤ) (F : MvLaurent r) (n : ℤ) :
    (curve β F).coeff n = F.coeff.sum fun a c => if β ⬝ᵥ a = n then c else 0 := by
  induction F using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add F G hF hG =>
    rw [map_add, coeff_add, Finsupp.add_apply, hF, hG, coeff_add,
      Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by split_ifs <;> simp)]
  | single a c =>
    rw [curve_single', coeff_single, coeff_single, Finsupp.sum_single_index (by simp),
      Finsupp.single_apply]

/-- If `a ↦ β·a` is injective at `a₀` on the support of `F`, the coefficient of `u^{a₀}`
survives restriction to the curve. -/
theorem coeff_curve_of_injOn (β : Fin r → ℤ) (F : MvLaurent r) (a₀ : Fin r → ℤ)
    (h : ∀ a ∈ F.coeff.support, β ⬝ᵥ a = β ⬝ᵥ a₀ → a = a₀) :
    (curve β F).coeff (β ⬝ᵥ a₀) = F.coeff a₀ := by
  rw [coeff_curve, Finsupp.sum, Finset.sum_eq_single a₀
    (fun b hb hne => ite_eq_right fun e => hne (h b hb e))
    (fun hnot => by simp [Finsupp.notMem_support_iff.1 hnot])]
  simp

/-- **Kronecker substitution.** Finitely many nonzero vectors of `ℤ^r` have nonzero dot
product with some `β ∈ ℤ^r` (take `βᵢ = Nⁱ` with `N` avoiding finitely many roots). -/
theorem exists_dotProduct_ne_zero (s : Finset (Fin r → ℤ)) (hs : ∀ v ∈ s, v ≠ 0) :
    ∃ β : Fin r → ℤ, ∀ v ∈ s, β ⬝ᵥ v ≠ 0 := by
  classical
  let pv : (Fin r → ℤ) → Polynomial ℤ := fun v => ∑ i : Fin r, Polynomial.monomial (i : ℕ) (v i)
  have hcoeff : ∀ v (i : Fin r), (pv v).coeff i = v i := fun v i => by
    simp only [pv, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single i (fun j _ hj => ite_eq_right fun e => hj (Fin.val_injective e))
      (by simp)]
    simp
  have hne : ∀ v ∈ s, pv v ≠ 0 := fun v hv h0 => by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 (hs v hv)
    exact hi (by rw [← hcoeff v i, h0, Polynomial.coeff_zero]; rfl)
  obtain ⟨N, hN⟩ := Infinite.exists_notMem_finset (s.biUnion fun v => (pv v).roots.toFinset)
  refine ⟨fun i => N ^ (i : ℕ), fun v hv h0 => hN (Finset.mem_biUnion.2 ⟨v, hv, ?_⟩)⟩
  rw [Multiset.mem_toFinset, Polynomial.mem_roots (hne v hv), Polynomial.IsRoot,
    ← h0, dotProduct]
  simp only [pv, Polynomial.eval_finsetSum, Polynomial.eval_monomial]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- A Laurent polynomial is non-constant: it has a nonzero monomial `u^a` with `a ≠ 0`. -/
def NonConst (F : MvLaurent r) : Prop := ∃ a, a ≠ 0 ∧ F.coeff a ≠ 0

/-- **Restriction to a generic monomial curve** (proof of Lemma 6, `r > 1`). For finitely
many Laurent polynomials there is `β ∈ ℤ^r` such that every non-constant one stays
non-constant on the curve `t ↦ t^β`. -/
theorem exists_curve_not_const {ι : Type*} [Finite ι] (F : ι → MvLaurent r) :
    ∃ β : Fin r → ℤ, ∀ i, NonConst (F i) →
      curve β (F i) ∉ Set.range (LaurentPolynomial.C : ℂ →+* LaurentPolynomial ℂ) := by
  classical
  cases nonempty_fintype ι
  let S : ι → Finset (Fin r → ℤ) := fun i => insert 0 (F i).coeff.support
  let s := Finset.univ.biUnion fun i =>
    (((S i) ×ˢ (S i)).filter fun p => p.1 ≠ p.2).image fun p => p.1 - p.2
  obtain ⟨β, hβ⟩ := exists_dotProduct_ne_zero s fun v hv => by
    obtain ⟨i, -, hv⟩ := Finset.mem_biUnion.1 hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
    exact sub_ne_zero.2 (Finset.mem_filter.1 hp).2
  have key : ∀ i, ∀ a ∈ S i, ∀ b ∈ S i, a ≠ b → β ⬝ᵥ a ≠ β ⬝ᵥ b := fun i a ha b hb hab e =>
    hβ (a - b) (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, Finset.mem_image.2
      ⟨(a, b), Finset.mem_filter.2 ⟨Finset.mem_product.2 ⟨ha, hb⟩, hab⟩, rfl⟩⟩)
      (by rw [dotProduct_sub, e, sub_self])
  refine ⟨β, fun i ⟨a, ha0, ha⟩ ⟨c, hc⟩ => ?_⟩
  have haS : a ∈ S i := Finset.mem_insert_of_mem (Finsupp.mem_support_iff.2 ha)
  have h1 := coeff_curve_of_injOn β (F i) a fun b hb e =>
    not_not.1 fun hne => key i b (Finset.mem_insert_of_mem hb) a haS hne e
  have h2 : β ⬝ᵥ a ≠ 0 := by
    have := key i a haS 0 (Finset.mem_insert_self _ _) ha0
    rwa [dotProduct_zero] at this
  rw [← hc, ← LaurentPolynomial.single_eq_C, coeff_single, Finsupp.single_apply,
    ite_eq_right (Ne.symm h2)] at h1
  exact ha h1.symm

/-- A nonzero one-variable Laurent polynomial is nonzero at some point of `ℂ^×`. -/
theorem exists_laurent_eval₂_ne_zero {f : LaurentPolynomial ℂ} (hf : f ≠ 0) :
    ∃ t : ℂˣ, LaurentPolynomial.eval₂ (RingHom.id ℂ) t f ≠ 0 := by
  obtain ⟨n, f', hf'⟩ := LaurentPolynomial.exists_T_pow f
  have hf'0 : f' ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hf'
    exact hf (by simpa [LaurentPolynomial.isUnit_T n |>.mul_left_eq_zero] using hf'.symm)
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (insert (0 : ℂ) f'.roots.toFinset)
  have ht0 : t ≠ 0 := fun h => ht (h ▸ Finset.mem_insert_self _ _)
  have htr : f'.eval t ≠ 0 := fun h => ht (Finset.mem_insert_of_mem
    (Multiset.mem_toFinset.2 ((Polynomial.mem_roots hf'0).2 h)))
  refine ⟨Units.mk0 t ht0, fun h => htr ?_⟩
  have := congrArg (LaurentPolynomial.eval₂ (RingHom.id ℂ) (Units.mk0 t ht0)) hf'
  rw [LaurentPolynomial.eval₂_toLaurent, map_mul, h, zero_mul] at this
  rw [Units.val_mk0] at this
  exact this

/-- A Laurent polynomial vanishing at every point of `(ℂ^×)^r` is zero. -/
theorem eq_zero_of_forall_evalHom {F : MvLaurent r} (h : ∀ x : Fin r → ℂˣ, evalHom x F = 0) :
    F = 0 := by
  classical
  by_contra hF
  obtain ⟨a₀, ha₀⟩ : ∃ a₀, F.coeff a₀ ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hF (AddMonoidAlgebra.ext (Finsupp.ext h'))
  let s := (F.coeff.support ×ˢ F.coeff.support).filter (fun p => p.1 ≠ p.2) |>.image
    fun p => p.1 - p.2
  obtain ⟨β, hβ⟩ := exists_dotProduct_ne_zero s fun v hv => by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
    exact sub_ne_zero.2 (Finset.mem_filter.1 hp).2
  have hc := coeff_curve_of_injOn β F a₀ fun b hb e => not_not.1 fun hne =>
    hβ (b - a₀) (Finset.mem_image.2 ⟨(b, a₀), Finset.mem_filter.2
      ⟨Finset.mem_product.2 ⟨hb, Finsupp.mem_support_iff.2 ha₀⟩, hne⟩, rfl⟩)
      (by rw [dotProduct_sub, e, sub_self])
  have hne : curve β F ≠ 0 := fun h0 => ha₀ (by rw [← hc, h0]; rfl)
  obtain ⟨t, ht⟩ := exists_laurent_eval₂_ne_zero hne
  exact ht (by rw [eval₂_curve]; exact h _)

end MvLaurent

end IngramMello
