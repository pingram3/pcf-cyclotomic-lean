import IngramMello.Escape
import IngramMello.EscapeArch
import IngramMello.Descent

/-!
# `IngramBound` from the local bounds (Proposition 3 of the paper)

Given an algebraic PCF monic centred polynomial `f`, choose a number field `L ⊆ ℂ` containing
its coefficients, its critical points and one fixed point. The ultrametric bound
(`exists_local_bound`) applied to every `𝔭`-adic valuation of `L` gives integrality of `D * a_k`
and of `D * (fⁿ(c) - fᵐ(c))`; the archimedean bound (`exists_arch_bound`) applied to every embedding
`σ : L → ℂ` (which preserves the PCF property) bounds the conjugates.
-/

namespace IngramMello

open Polynomial NumberField

section Transport

theorem iterate_eval_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (q : R[X])
    (w : R) (n : ℕ) :
    φ ((fun z => q.eval z)^[n] w) = (fun z => (q.map φ).eval z)^[n] (φ w) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih, eval_map, eval₂_hom]

theorem hasFiniteOrbit_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (q : R[X])
    (w : R) (h : HasFiniteOrbit q w) : HasFiniteOrbit (q.map φ) (φ w) := by
  unfold HasFiniteOrbit at h ⊢
  refine (h.image φ).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨(fun z => aeval z q)^[n] w, ⟨n, rfl⟩, ?_⟩
  simp only [coe_aeval_eq_eval]
  exact iterate_eval_map φ q w n

theorem hasFiniteOrbit_of_map {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (hφ : Function.Injective φ) (q : R[X]) (w : R) (h : HasFiniteOrbit (q.map φ) (φ w)) :
    HasFiniteOrbit q w := by
  unfold HasFiniteOrbit at h ⊢
  refine Set.Finite.of_finite_image (f := φ) ?_ hφ.injOn
  refine h.subset ?_
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  refine ⟨n, ?_⟩
  simp only [coe_aeval_eq_eval]
  exact (iterate_eval_map φ q w n).symm

end Transport

/-- **Proposition 3 of the paper** (Ingram's adelic bound), in the integral form `IngramBound`. -/
theorem ingramBound_of_local : IngramBound := by
  intro d hd
  obtain ⟨N, hN, hloc⟩ := exists_local_bound.{0, 0} d hd
  obtain ⟨MG, hMG⟩ := exists_arch_bound d hd
  refine ⟨N, hN, N * MG, ?_⟩
  intro a halg hpcf
  set f := monicCentred d a with hf
  have hfm : f.Monic := monicCentred_monic hd a
  have hfdeg : f.natDegree = d := monicCentred_natDegree hd a
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  /- Critical points and a fixed point over `ℂ`. -/
  obtain ⟨g₀, hg₀m, hg₀deg, hfg₀⟩ := exists_derivative_monicCentred hd a
  obtain ⟨c, rfl⟩ := exists_eq_critProd hg₀m hg₀deg
  have hc : derivative f = C (d : ℂ) * critProd c := hfg₀
  have hcroot : ∀ i, (derivative f).IsRoot (c i) := fun i => by
    rw [hc, IsRoot, eval_mul, (critProd_isRoot_iff c (c i)).mpr ⟨i, rfl⟩, mul_zero]
  have hroot_c : ∀ z, (derivative f).IsRoot z → ∃ i, c i = z := by
    intro z hz
    rw [hc, IsRoot, eval_mul, eval_C] at hz
    exact (critProd_isRoot_iff c z).mp ((mul_eq_zero.mp hz).resolve_left hd0)
  have hf'ne : derivative f ≠ 0 := by
    rw [hc]; exact mul_ne_zero (C_ne_zero.mpr hd0) (critProd_monic c).ne_zero
  obtain ⟨p, hp⟩ : ∃ p : ℂ, f.eval p = p := by
    have hdeg : 0 < (f - X).degree := by
      rw [degree_sub_eq_left_of_degree_lt]
      · rw [degree_eq_natDegree hfm.ne_zero, hfdeg]; exact_mod_cast (show 0 < d by omega)
      · rw [degree_X, degree_eq_natDegree hfm.ne_zero, hfdeg]
        exact_mod_cast (show 1 < d by omega)
    obtain ⟨p, hp⟩ := Complex.exists_root hdeg
    exact ⟨p, by rw [IsRoot, eval_sub, eval_X, sub_eq_zero] at hp; exact hp⟩
  /- The number field `K₀ = ℚ(a)`; roots of `f'` and `p` are algebraic. -/
  set K₀ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range a) with hK₀
  have : FiniteDimensional ℚ K₀ := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro _ ⟨i, rfl⟩
    exact (halg i).isIntegral
  have haK₀ : ∀ i, a i ∈ K₀ := fun i => IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩
  set a₀ : Fin (d - 1) → K₀ := fun i => ⟨a i, haK₀ i⟩ with ha₀
  have hf₀ : (monicCentred d a₀).map (algebraMap K₀ ℂ) = f := by rw [map_monicCentred]; rfl
  have hint : ∀ z : ℂ, (derivative f).IsRoot z → IsIntegral ℚ z := by
    intro z hz
    have hq : derivative (monicCentred d a₀) ≠ 0 := by
      intro h0
      apply hf'ne
      have := congrArg (Polynomial.map (algebraMap K₀ ℂ)) h0
      rwa [← derivative_map, hf₀, Polynomial.map_zero] at this
    have hzalg : IsAlgebraic K₀ z :=
      ⟨derivative (monicCentred d a₀), hq, by
        rw [aeval_def, ← eval_map, ← derivative_map, hf₀]; exact hz⟩
    exact isIntegral_trans (R := ℚ) (A := K₀) z hzalg.isIntegral
  have hpint : IsIntegral ℚ p := by
    have hq : monicCentred d a₀ - X ≠ 0 := by
      intro h0
      have := congrArg (Polynomial.map (algebraMap K₀ ℂ)) h0
      rw [Polynomial.map_sub, hf₀, map_X, Polynomial.map_zero, sub_eq_zero] at this
      have h1 := congrArg natDegree this
      rw [hfdeg, natDegree_X] at h1
      omega
    have hpalg : IsAlgebraic K₀ p :=
      ⟨monicCentred d a₀ - X, hq, by
        rw [aeval_def, ← eval_map, Polynomial.map_sub, hf₀, map_X, eval_sub, eval_X, hp, sub_self]⟩
    exact isIntegral_trans (R := ℚ) (A := K₀) p hpalg.isIntegral
  /- The number field `L`. -/
  set S : Set ℂ := Set.range a ∪ {z | (derivative f).IsRoot z} ∪ {p} with hS
  have hSfin : S.Finite :=
    ((Set.finite_range a).union (finite_setOf_isRoot hf'ne)).union (Set.finite_singleton p)
  set L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ S with hL
  have : FiniteDimensional ℚ L := by
    have := hSfin.to_subtype
    apply IntermediateField.finiteDimensional_adjoin
    intro x hx
    rcases hx with (⟨i, rfl⟩ | hx) | rfl
    · exact (halg i).isIntegral
    · exact hint x hx
    · exact hpint
  have : NumberField L := ⟨⟩
  have hmemL : ∀ x ∈ S, x ∈ L := fun x hx => IntermediateField.subset_adjoin ℚ S hx
  have haL : ∀ i, a i ∈ L := fun i => hmemL _ (Or.inl (Or.inl ⟨i, rfl⟩))
  have hcL : ∀ i, c i ∈ L := fun i => hmemL _ (Or.inl (Or.inr (hcroot i)))
  have hpL : p ∈ L := hmemL p (Or.inr rfl)
  set aL : Fin (d - 1) → L := fun i => ⟨a i, haL i⟩ with haL'
  set cL : Fin (d - 1) → L := fun i => ⟨c i, hcL i⟩ with hcL'
  set pL : L := ⟨p, hpL⟩ with hpL'
  set fL := monicCentred d aL with hfL'
  have hfL : fL.map (algebraMap L ℂ) = f := by rw [hfL', map_monicCentred]; rfl
  have hinj : Function.Injective (algebraMap L ℂ) := (algebraMap L ℂ).injective
  have hcLder : derivative fL = C (d : L) * critProd cL := by
    apply Polynomial.map_injective _ hinj
    rw [← derivative_map, hfL, hc, Polynomial.map_mul, map_C, map_critProd, map_natCast]
    rfl
  have hpLfix : fL.eval pL = pL := by
    apply hinj
    rw [← eval₂_hom, ← eval_map, hfL]
    exact hp
  have horbL : ∀ i, HasFiniteOrbit fL (cL i) := fun i =>
    hasFiniteOrbit_of_map (algebraMap L ℂ) hinj fL (cL i) (by rw [hfL]; exact hpcf (c i) (hcroot i))
  /- Integrality from the ultrametric bound at every finite place. -/
  have hval := fun (v : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) =>
    hloc L (WithZero (Multiplicative ℤ)) (v.valuation L) aL cL pL hcLder hpLfix horbL
  have hintL : ∀ x : L, (∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 L), v.valuation L x ≤ 1) →
      IsIntegral ℤ (algebraMap L ℂ x) := by
    intro x hx
    obtain ⟨y, hy⟩ :=
      IsDedekindDomain.HeightOneSpectrum.mem_integers_of_valuation_le_one (R := 𝓞 L) (K := L) x hx
    rw [← hy]
    exact (RingOfIntegers.isIntegral_coe y).map (algebraMap L ℂ).toIntAlgHom
  /- Conjugates from the archimedean bound at every embedding. -/
  have hhouse : ∀ x : L, (∀ σ : L →ₐ[ℚ] ℂ, ‖σ x‖ ≤ N * MG) →
      HouseLE (algebraMap L ℂ x) (N * MG) :=
    fun x hx => (houseLE_iff_embeddings L.val x _).mpr hx
  have hmapσ : ∀ σ : L →ₐ[ℚ] ℂ, fL.map (σ : L →+* ℂ) = monicCentred d (fun i => σ (aL i)) :=
    fun σ => map_monicCentred _ d aL
  have hσder : ∀ σ : L →ₐ[ℚ] ℂ, derivative (monicCentred d (fun i => σ (aL i)))
      = C (d : ℂ) * critProd (fun i => σ (cL i)) := by
    intro σ
    rw [← hmapσ, derivative_map, hcLder, Polynomial.map_mul, map_C, map_critProd, map_natCast]
    rfl
  have hσroot : ∀ (σ : L →ₐ[ℚ] ℂ) i,
      (derivative (monicCentred d (fun i => σ (aL i)))).IsRoot (σ (cL i)) := fun σ i => by
    rw [hσder, IsRoot, eval_mul, (critProd_isRoot_iff _ (σ (cL i))).mpr ⟨i, rfl⟩, mul_zero]
  have hσpcf : ∀ σ : L →ₐ[ℚ] ℂ, IsPCF (monicCentred d (fun i => σ (aL i))) := by
    intro σ z hz
    rw [hσder, IsRoot, eval_mul, eval_C] at hz
    obtain ⟨i, rfl⟩ := (critProd_isRoot_iff _ z).mp ((mul_eq_zero.mp hz).resolve_left hd0)
    rw [← hmapσ]
    exact hasFiniteOrbit_map (σ : L →+* ℂ) fL (cL i) (horbL i)
  refine ⟨?_, ?_⟩
  · intro i
    have hx : (N : ℂ) * a i = algebraMap L ℂ ((N : L) * aL i) := by
      rw [map_mul, map_natCast]; rfl
    rw [hx]
    refine ⟨hintL _ fun v => (hval v).1 i, hhouse _ fun σ => ?_⟩
    rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left ((hMG _ (hσpcf σ)).1 i) (Nat.cast_nonneg N)
  · intro z hz n m
    obtain ⟨i, rfl⟩ := hroot_c z hz
    have hx : (N : ℂ) * ((fun w => f.eval w)^[n] (c i) - (fun w => f.eval w)^[m] (c i))
        = algebraMap L ℂ ((N : L) *
          ((fun w => fL.eval w)^[n] (cL i) - (fun w => fL.eval w)^[m] (cL i))) := by
      rw [map_mul, map_natCast, map_sub, iterate_eval_map, iterate_eval_map, hfL]
      rfl
    rw [hx]
    refine ⟨hintL _ fun v => (hval v).2 (cL i) (horbL i) n m, hhouse _ fun σ => ?_⟩
    have h1 := iterate_eval_map (σ : L →+* ℂ) fL (cL i) n
    have h2 := iterate_eval_map (σ : L →+* ℂ) fL (cL i) m
    simp only [AlgHom.coe_toRingHom] at h1 h2
    rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast, map_sub, h1, h2, hmapσ]
    exact mul_le_mul_of_nonneg_left ((hMG _ (hσpcf σ)).2 (σ (cL i)) (hσroot σ i) n m)
      (Nat.cast_nonneg N)

end IngramMello
