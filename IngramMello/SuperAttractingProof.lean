import Mathlib
import IngramMello.Resultants
import IngramMello.IngramBound
import IngramMello.SuperAttractingAlg

/-!
# Super-attracting parameters: assembly (Lemma 6 of the paper, one-parameter case)

This file proves the statement `SuperAttracting` of `Inputs.lean` by an algebraic argument,
without complex dynamics: the inputs from Dujardin–Favre and Branner–Hubbard used in the paper's
proof are replaced by valuation theory at two places of a finite extension of `ℂ(t)`.

* `exists_escapes_of_nonconst`: for a non-isotrivial family some critical point escapes at one
  of the two places of `E` (via `exists_local_coeff_bound_of_not_escapes` and
  `TwoPlaces.mem_range_C_of_le_one`).
* `superAttracting_of_algebraic`: the statement `SuperAttracting`. `P := A` is the
  infinite-orbit factor of `f'/d` from `exists_infiniteOrbitFactor`; the periodic specialization
  comes from the main lemma of `SuperAttractingAlg.lean` applied to the resultants
  `W_{q,0} = Res(A, f^q(X) − X) ∈ ℂ[t,t⁻¹]`: if none of them had a zero in `ℂˣ`,
  `TwoPlaces.val_mul_val_eq_one_of_forall_eval_ne_zero` would give `w₀(W_q) w₁(W_q) = 1` for
  all `q ≥ 1`, contradicting the main lemma.
-/

namespace IngramMello

open Polynomial

section Helpers

/-- Over an algebraically closed field, a monic polynomial of degree `n` is `critProd u`. -/
theorem exists_eq_critProd_of_isAlgClosed {K : Type*} [Field K] [IsAlgClosed K] {g : K[X]}
    (hg : g.Monic) {n : ℕ} (hn : g.natDegree = n) : ∃ u : Fin n → K, g = critProd u := by
  classical
  have hcard : Multiset.card g.roots = n := by rw [IsAlgClosed.card_roots_eq_natDegree, hn]
  set L := g.roots.toList with hL
  have hlen : L.length = n := by rw [hL, Multiset.length_toList, hcard]
  refine ⟨fun i => L.get (Fin.cast hlen.symm i), ?_⟩
  have hofn : List.ofFn (fun i : Fin n => L.get (Fin.cast hlen.symm i)) = L := by
    apply List.ext_get (by simp [hlen])
    intro m h₁ h₂
    simp
  have hprod : (g.roots.map fun a => X - C a).prod = g := by
    have := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := g) IsAlgClosed.card_roots_eq_natDegree
    rwa [hg.leadingCoeff, C_1, one_mul] at this
  unfold critProd
  rw [← List.prod_ofFn]
  have hmap : List.ofFn (fun i : Fin n => X - C (L.get (Fin.cast hlen.symm i)))
      = L.map (fun a => X - C a) := by
    calc List.ofFn (fun i : Fin n => X - C (L.get (Fin.cast hlen.symm i)))
        = (List.ofFn fun i : Fin n => L.get (Fin.cast hlen.symm i)).map (fun a => X - C a) :=
          by rw [List.map_ofFn]; rfl
      _ = L.map (fun a => X - C a) := by rw [hofn]
  rw [hmap, ← Multiset.prod_coe, ← Multiset.map_coe, hL, Multiset.coe_toList, hprod]

/-- If every root (in an algebraically closed `L ⊇ E`) of a monic `g ∈ E[X]` of degree `n`
lies in `E`, then `g = critProd c` for some `c : Fin n → E`. -/
theorem exists_eq_critProd_of_roots_mem {E L : Type*} [Field E] [Field L] [IsAlgClosed L]
    [Algebra E L] {g : E[X]} (hg : g.Monic) {n : ℕ} (hn : g.natDegree = n)
    (hroots : ∀ z : L, (g.map (algebraMap E L)).IsRoot z → z ∈ Set.range (algebraMap E L)) :
    ∃ c : Fin n → E, g = critProd c := by
  obtain ⟨u, hu⟩ := exists_eq_critProd_of_isAlgClosed (hg.map (algebraMap E L))
    (by rw [hg.natDegree_map, hn])
  have hmem : ∀ i, u i ∈ Set.range (algebraMap E L) := fun i =>
    hroots (u i) (by rw [hu]; exact (critProd_isRoot_iff u (u i)).mpr ⟨i, rfl⟩)
  choose c hc using hmem
  refine ⟨c, Polynomial.map_injective _ (algebraMap E L).injective ?_⟩
  rw [hu, map_critProd]
  congr 1
  funext i
  exact (hc i).symm

theorem roots_critProd {F : Type*} [Field F] {n : ℕ} (u : Fin n → F) :
    (critProd u).roots = Finset.univ.val.map u := by
  unfold critProd
  rw [Finset.prod_eq_multiset_prod,
    show (fun i => X - C (u i)) = (fun a => X - C a) ∘ u from rfl, ← Multiset.map_map,
    roots_multiset_prod_X_sub_C]

/-- The specialization formula for `W_{q,0}` in a field `E` where `A_E = critProd cA`. -/
theorem algebraMap_W_eq_prod {R₀ E L : Type*} [CommRing R₀] [Field E] [Field L] [IsAlgClosed L]
    [Algebra E L] [Algebra R₀ E] [Algebra R₀ L] [IsScalarTower R₀ E L]
    {A : R₀[X]} (hA : A.Monic) (f : R₀[X]) {k : ℕ} (cA : Fin k → E)
    (hcA : A.map (algebraMap R₀ E) = critProd cA) (q : ℕ) :
    algebraMap R₀ E (W A f q 0) =
      ∏ j, ((fun z => (f.map (algebraMap R₀ E)).eval z)^[q] (cA j) - cA j) := by
  apply (algebraMap E L).injective
  have hAL : A.map (algebraMap R₀ L) = critProd ((algebraMap E L) ∘ cA) := by
    rw [IsScalarTower.algebraMap_eq R₀ E L, ← Polynomial.map_map, hcA, map_critProd]
  have hfL : f.map (algebraMap R₀ L) = (f.map (algebraMap R₀ E)).map (algebraMap E L) := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
  rw [← IsScalarTower.algebraMap_apply, ev_W hA f (algebraMap R₀ L) q 0, hAL, roots_critProd,
    Multiset.map_map, ← Finset.prod_eq_multiset_prod, map_prod]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, Function.iterate_zero, id_eq, map_sub]
  rw [iterate_eval_map, hfL]

end Helpers

/-! ### Some critical point escapes -/

section Escapes

variable {E : Type*} [Field E] [CharZero E] [Algebra Kt E] [FiniteDimensional Kt E]
  [Algebra (LaurentPolynomial ℂ) E] [IsScalarTower (LaurentPolynomial ℂ) Kt E]

/-- **An escaping critical point.** If some coefficient `a i` is nonconstant, some critical
point `c i` escapes at `w₀` or at `w₁`. -/
theorem exists_escapes_of_nonconst {w₀ w₁ : Valuation E (WithZero (Multiplicative ℤ))}
    (hw : TwoPlaces E w₀ w₁) {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → LaurentPolynomial ℂ)
    (hnc : ∃ i, a i ∉ Set.range (LaurentPolynomial.C : ℂ →+* LaurentPolynomial ℂ))
    (c : Fin (d - 1) → E)
    (hc : derivative (monicCentred d fun i => algebraMap (LaurentPolynomial ℂ) E (a i))
      = C (d : E) * critProd c)
    (p : E) (hp : (monicCentred d fun i => algebraMap (LaurentPolynomial ℂ) E (a i)).eval p = p) :
    ∃ i, Escapes w₀ (monicCentred d fun i => algebraMap (LaurentPolynomial ℂ) E (a i)) (c i) ∨
      Escapes w₁ (monicCentred d fun i => algebraMap (LaurentPolynomial ℂ) E (a i)) (c i) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨N, hN, hbound⟩ := exists_local_coeff_bound_of_not_escapes d hd
  have h0 := hbound E _ w₀ _ c p hc hp fun i => (hcon i).1
  have h1 := hbound E _ w₁ _ c p hc hp fun i => (hcon i).2
  obtain ⟨i, hi⟩ := hnc
  apply hi
  obtain ⟨hN0, hN1⟩ := hw.val_natCast hN.ne'
  refine hw.mem_range_C_of_le_one ?_ ?_
  · have := h0 i; rwa [Valuation.map_mul, hN0, one_mul] at this
  · have := h1 i; rwa [Valuation.map_mul, hN1, one_mul] at this

end Escapes

/-! ### The one-parameter statement -/

/-- **`SuperAttracting`** (Lemma 6 of the paper for `r = 1`), proved algebraically, without
complex dynamics. -/
theorem superAttracting_of_algebraic : SuperAttracting := by
  classical
  intro d hd a hnc
  set f : (LaurentPolynomial ℂ)[X] := monicCentred d a with hf
  have hfm : f.Monic := monicCentred_monic hd a
  have hfdeg : f.natDegree = d := monicCentred_natDegree hd a
  haveI : IsIntegrallyClosed (LaurentPolynomial ℂ) := isIntegrallyClosed_laurentPolynomial ℂ
  obtain ⟨g, hgm, hgdeg, hfg⟩ := exists_derivative_monicCentred hd a
  obtain ⟨A, B, n, m, N, hAm, hBm, hgAB, hnm, hBdvd, hAroots⟩ := exists_infiniteOrbitFactor f g hgm
  set ι : LaurentPolynomial ℂ →+* GenericField :=
    (algebraMap Kt GenericField).comp (algebraMap (LaurentPolynomial ℂ) Kt) with hι
  have hι_eq : ι = algebraMap (LaurentPolynomial ℂ) GenericField :=
    (IsScalarTower.algebraMap_eq (LaurentPolynomial ℂ) Kt GenericField).symm
  have hιinj : Function.Injective ι :=
    (algebraMap Kt GenericField).injective.comp (IsFractionRing.injective _ Kt)
  haveI : CharZero GenericField := charZero_of_injective_ringHom (ι.comp LaurentPolynomial.C).injective
  have hFL : (fun w : GenericField => aeval w f) = fun z => (f.map ι).eval z := by
    funext w; rw [aeval_def, eval₂_eq_eval_map, hι_eq]
  refine ⟨A, hAm, fun c hc => ⟨?_, ?_⟩, ?_⟩
  · rw [hfg, hgAB, map_mul, map_mul, hc, zero_mul, mul_zero]
  · have hcA : (A.map ι).IsRoot c := by rwa [aeval_def, eval₂_eq_eval_map, ← hι_eq] at hc
    unfold HasFiniteOrbit
    rw [hFL]
    exact hAroots c hcA
  /- The field `E`. -/
  haveI : CharZero (LaurentPolynomial ℂ) :=
    charZero_of_injective_ringHom (LaurentPolynomial.C (R := ℂ)).injective
  set h : Kt[X] := (derivative f * (f - X)).map (algebraMap (LaurentPolynomial ℂ) Kt) with hh
  have hf'ne : derivative f ≠ 0 := by
    rw [hfg]
    exact mul_ne_zero (C_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hgm.ne_zero
  have hfXne : f - X ≠ 0 := by
    intro h0
    have h1 := congrArg natDegree (sub_eq_zero.mp h0)
    rw [hfdeg, natDegree_X] at h1
    omega
  have hhne : h ≠ 0 := by
    rw [hh, Polynomial.map_ne_zero_iff (IsFractionRing.injective _ Kt)]
    exact mul_ne_zero hf'ne hfXne
  set E : IntermediateField Kt GenericField :=
    IntermediateField.adjoin Kt (h.rootSet GenericField) with hE
  haveI : FiniteDimensional Kt E := by
    haveI := (h.rootSet_finite GenericField).to_subtype
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    rw [mem_rootSet] at hx
    exact IsAlgebraic.isIntegral ⟨h, hx.1, hx.2⟩
  haveI : IsScalarTower (LaurentPolynomial ℂ) E GenericField :=
    IsScalarTower.of_algebraMap_eq fun x => by
      rw [IsScalarTower.algebraMap_apply (LaurentPolynomial ℂ) Kt GenericField,
        IsScalarTower.algebraMap_apply (LaurentPolynomial ℂ) Kt E,
        ← IsScalarTower.algebraMap_apply Kt E GenericField]
  haveI : CharZero E := charZero_of_injective_ringHom
    ((algebraMap (LaurentPolynomial ℂ) E).comp LaurentPolynomial.C).injective
  have hιE : ∀ x, algebraMap E GenericField (algebraMap (LaurentPolynomial ℂ) E x) = ι x := by
    intro x
    rw [hι_eq, ← IsScalarTower.algebraMap_apply]
  have hmapE : ∀ P : (LaurentPolynomial ℂ)[X],
      (P.map (algebraMap (LaurentPolynomial ℂ) E)).map (algebraMap E GenericField) = P.map ι := by
    intro P
    rw [Polynomial.map_map, hι_eq, IsScalarTower.algebraMap_eq (LaurentPolynomial ℂ) E GenericField]
  have hmemE : ∀ z : GenericField, ((derivative f * (f - X)).map ι).IsRoot z →
      z ∈ Set.range (algebraMap E GenericField) := by
    intro z hz
    have hzE : z ∈ E := by
      refine IntermediateField.subset_adjoin Kt _ ?_
      rw [mem_rootSet]
      refine ⟨hhne, ?_⟩
      rw [aeval_def, eval₂_eq_eval_map, hh, Polynomial.map_map, ← hι]
      exact hz
    exact ⟨⟨z, hzE⟩, rfl⟩
  /- Critical points and a fixed point in `E`. -/
  set fE := f.map (algebraMap (LaurentPolynomial ℂ) E) with hfE
  have hfE' : fE = monicCentred d fun i => algebraMap (LaurentPolynomial ℂ) E (a i) := by
    rw [hfE, hf, map_monicCentred]
  have hfEm : fE.Monic := hfm.map _
  have hfEdeg : fE.natDegree = d := by rw [hfE, hfm.natDegree_map, hfdeg]
  set gE := g.map (algebraMap (LaurentPolynomial ℂ) E) with hgE
  have hgEm : gE.Monic := hgm.map _
  obtain ⟨c, hcg⟩ : ∃ c : Fin (d - 1) → E, gE = critProd c := by
    refine exists_eq_critProd_of_roots_mem (L := GenericField) hgEm
      (by rw [hgE, hgm.natDegree_map, hgdeg])
      fun z hz => ?_
    refine hmemE z ?_
    rw [hgE, hmapE] at hz
    rw [Polynomial.map_mul, IsRoot, eval_mul, hfg, Polynomial.map_mul, eval_mul, hz.eq_zero,
      mul_zero, zero_mul]
  have hcE : derivative fE = C (d : E) * critProd c := by
    rw [hfE, derivative_map, hfg, Polynomial.map_mul, map_C, map_natCast, ← hgE, hcg]
  obtain ⟨p, hp⟩ : ∃ p : E, fE.eval p = p := by
    have hdeg : ((f - X).map ι).degree ≠ 0 := by
      rw [degree_eq_natDegree (Polynomial.map_ne_zero_iff hιinj |>.mpr hfXne),
        natDegree_map_eq_of_injective hιinj]
      have : (f - X).natDegree = d := by
        rw [natDegree_sub_eq_left_of_natDegree_lt (by rw [natDegree_X, hfdeg]; omega), hfdeg]
      rw [this]
      exact_mod_cast (show d ≠ 0 by omega)
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_root _ hdeg
    obtain ⟨pE, hpE⟩ := hmemE z (by
      rw [Polynomial.map_mul, IsRoot, eval_mul, hz.eq_zero, mul_zero])
    refine ⟨pE, (algebraMap E GenericField).injective ?_⟩
    have h1 := iterate_eval_map (algebraMap E GenericField) fE pE 1
    simp only [Function.iterate_one] at h1
    rw [h1, hpE, hfE, hmapE]
    have := hz.eq_zero
    rw [Polynomial.map_sub, map_X, eval_sub, eval_X, sub_eq_zero] at this
    exact this
  /- The two places and the escaping critical point. -/
  obtain ⟨w₀, w₁, hw⟩ := exists_twoPlaces E
  obtain ⟨i₀, hi₀⟩ := exists_escapes_of_nonconst hw hd a hnc c (hfE' ▸ hcE) p (hfE' ▸ hp)
  rw [← hfE'] at hi₀
  /- The roots of `A` in `E`. -/
  set AE := A.map (algebraMap (LaurentPolynomial ℂ) E) with hAE
  have hAEm : AE.Monic := hAm.map _
  obtain ⟨cA, hcA⟩ : ∃ cA : Fin A.natDegree → E, AE = critProd cA := by
    refine exists_eq_critProd_of_roots_mem (L := GenericField) hAEm
      (by rw [hAE, hAm.natDegree_map]) fun z hz => ?_
    refine hmemE z ?_
    rw [hAE, hmapE] at hz
    rw [Polynomial.map_mul, IsRoot, eval_mul, hfg, Polynomial.map_mul, eval_mul, hgAB,
      Polynomial.map_mul, eval_mul, hz.eq_zero, zero_mul, mul_zero, zero_mul]
  set FE := fun z : E => fE.eval z with hFE
  set FL := fun z : GenericField => (f.map ι).eval z with hFL'
  have hiter : ∀ (x : E) (k : ℕ), algebraMap E GenericField (FE^[k] x) = FL^[k] (algebraMap E GenericField x) := by
    intro x k
    rw [hFE, hFL', iterate_eval_map, hfE, hmapE]
  have hAroot_cA : ∀ j, (A.map ι).IsRoot (algebraMap E GenericField (cA j)) := by
    intro j
    rw [← hmapE, ← hAE, hcA, map_critProd]
    exact (critProd_isRoot_iff _ _).mpr ⟨j, rfl⟩
  have hper : ∀ j (g' : ℕ), 0 < g' → FE^[g'] (cA j) ≠ cA j := by
    intro j g' hg' heq
    apply hAroots _ (hAroot_cA j)
    have := congrArg (algebraMap E GenericField) heq
    rw [hiter] at this
    exact finite_orbit_of_iterate_eq FL (show g' ≠ 0 by omega) this
  -- the escaping critical point is a root of `A_E`
  have hesc_i₀ : Escapes w₀ fE (c i₀) ∨ Escapes w₁ fE (c i₀) := hi₀
  have hci₀_inf : ¬ HasFiniteOrbit fE (c i₀) := by
    rcases hesc_i₀ with h | h
    · exact not_hasFiniteOrbit_of_escapes w₀ hfEm (by rw [hfEdeg]; exact hd) h
    · exact not_hasFiniteOrbit_of_escapes w₁ hfEm (by rw [hfEdeg]; exact hd) h
  have hci₀_A : AE.IsRoot (c i₀) := by
    refine isRoot_of_iterate_ne hgAB hBdvd (algebraMap (LaurentPolynomial ℂ) E) ?_ ?_
    · rw [← hgE, hcg]; exact (critProd_isRoot_iff _ _).mpr ⟨i₀, rfl⟩
    · intro heq
      apply hci₀_inf
      unfold HasFiniteOrbit
      have : (fun w : E => aeval w fE) = FE := by funext w; rw [hFE, coe_aeval_eq_eval]
      rw [this]
      exact finite_orbit_of_iterate_eq FE hnm heq
  obtain ⟨j₀, hj₀⟩ := (critProd_isRoot_iff cA (c i₀)).mp (hcA ▸ hci₀_A)
  /- The main lemma forbids `W_{q,0}` being a unit for all `q ≥ 1`. -/
  by_contra hcon
  push Not at hcon
  have hno : ∀ q, 0 < q → ∀ t₀ : ℂˣ,
      LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀ (W A f q 0) ≠ 0 := by
    intro q hq t₀ h0
    have hev := ev_W hAm f (LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀) q 0
    rw [h0, eq_comm, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hev
    obtain ⟨c₀, hc₀, hc₀0⟩ := hev
    simp only [Function.iterate_zero, id_eq, sub_eq_zero] at hc₀0
    exact hcon t₀ c₀ q hq ((mem_roots (hAm.map _).ne_zero).mp hc₀) hc₀0
  have hWeq : ∀ q, algebraMap (LaurentPolynomial ℂ) E (W A f q 0) = ∏ j, (FE^[q] (cA j) - cA j) :=
    fun q => algebraMap_W_eq_prod (L := GenericField) hAm f cA hcA q
  have hWne : ∀ q, 0 < q → W A f q 0 ≠ 0 := by
    intro q hq h0
    have := hWeq q
    rw [h0, map_zero, eq_comm, Finset.prod_eq_zero_iff] at this
    obtain ⟨j, -, hj⟩ := this
    exact hper j q hq (sub_eq_zero.mp hj)
  let wv : Fin 2 → Valuation E (WithZero (Multiplicative ℤ)) := ![w₀, w₁]
  refine false_of_escapes_of_prod_val_eq_one hfEm (by rw [hfEdeg]; exact hd)
    (ι := Fin A.natDegree × Fin 2)
    (fun jb => wv jb.2) (fun jb => cA jb.1) (fun jb g' hg' => hper jb.1 g' hg') ?_ ?_
  · rcases hesc_i₀ with h | h
    · exact ⟨(j₀, 0), by simpa [wv, hj₀] using h⟩
    · exact ⟨(j₀, 1), by simpa [wv, hj₀] using h⟩
  · intro q hq
    rw [Fintype.prod_prod_type]
    simp only [Fin.prod_univ_two]
    rw [Finset.prod_mul_distrib]
    simp only [wv, Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [← map_prod, ← map_prod, ← hWeq]
    exact hw.val_mul_val_eq_one_of_forall_eval_ne_zero (hWne q hq) (hno q hq)

end IngramMello
