import IngramMello.Projection
import IngramMello.Hajos
import IngramMello.SuperAttracting
import IngramMello.LinearForm

/-!
# Lemma 9: there are no exceptional families

Strong induction on the dimension `r`. Given an exceptional family, Lemma 7 supplies a
resultant `W` of high order at some point `x`, and Dvornicich–Zannier writes its torsion
specializations as short sums of roots of unity. Adjoining those roots of unity as new
coordinates and applying Laurent's theorem gives a torsion coset `C`. If the projection of
`C` to the original coordinates is dominant, pulling back to `C` produces a nonzero Laurent
polynomial with at most `N` monomials and order `> N` (contradicting Hajós, Lemma 5);
otherwise the projection lies in a smaller torsion coset, and pulling back along it gives
an exceptional family of smaller dimension (`isExceptional_descent`).
-/

namespace IngramMello

open AddMonoidAlgebra

namespace MvLaurent

/-- **Lemma 9, dominant case.** Let `F ∈ ℂ[ℤ^r]` be nonzero with `ord_x F ≥ N + 1`.
Suppose that on the coset `η w^B ⊆ (ℂ^×)^{r+N}`, whose projection to the first `r`
coordinates is dominant, `F` of the first `r` coordinates equals a fixed linear
combination of the last `N` coordinates. Then pulling back gives a nonzero Laurent
polynomial with at most `N` monomials and order `≥ N + 1`, contradicting Hajós. -/
theorem false_of_dominant_coset {r N s : ℕ} (F : MvLaurent r) (hF : F ≠ 0) (x : Fin r → ℂˣ)
    (hFx : F ∈ maxIdeal x ^ (N + 1)) (c : Fin N → ℂ) (η : Fin (r + N) → ℂˣ)
    (B : Matrix (Fin (r + N)) (Fin s) ℤ)
    (hBtop : Function.Injective (B.submatrix (Fin.castAdd N) id).transpose.mulVec)
    (hid : ∀ w : Fin s → ℂˣ, evalHom (fun j => monomialMap η B w (Fin.castAdd N j)) F =
      ∑ i, c i * (monomialMap η B w (Fin.natAdd r i) : ℂ)) : False := by
  let ηt : Fin r → ℂˣ := fun j => η (Fin.castAdd N j)
  let Bt := B.submatrix (Fin.castAdd N) id
  obtain ⟨z, hz⟩ := exists_monomialMap_eq ηt Bt hBtop x
  let H : MvLaurent s :=
    ∑ i, single (fun k => B (Fin.natAdd r i) k) (c i * η (Fin.natAdd r i))
  have hPH : pullback ηt Bt F = H := by
    rw [← sub_eq_zero]
    apply eq_zero_of_forall_evalHom
    intro w
    rw [map_sub, evalHom_pullback, sub_eq_zero]
    refine (hid w).trans ?_
    simp only [H, map_sum, evalHom_single, monomialMap, Units.val_mul, Units.coe_prod,
      Units.val_zpow_eq_zpow_val, mul_assoc]
  have hne : H ≠ 0 := by
    rw [← hPH]
    intro h0
    exact hF (pullback_injective ηt Bt hBtop (h0.trans (map_zero _).symm))
  have hmem : H ∈ maxIdeal z ^ (N + 1) := by
    rw [← hPH]
    exact pullback_mem_pow ηt Bt z (hz ▸ hFx)
  exact hajos_sum z le_rfl _ _ hne (Ideal.pow_le_pow_right N.le_succ hmem)

/-- A Laurent polynomial without non-constant monomials evaluates to its constant term. -/
theorem evalHom_of_not_nonConst {r : ℕ} {F : MvLaurent r} (hF : ¬ NonConst F)
    (x : Fin r → ℂˣ) : evalHom x F = F.coeff 0 := by
  have hF' : F = single 0 (F.coeff 0) := by
    refine AddMonoidAlgebra.ext (Finsupp.ext fun e => ?_)
    rw [coeff_single, Finsupp.single_apply]
    split_ifs with h
    · rw [h]
    · exact not_not.1 fun hne => hF ⟨e, Ne.symm h, hne⟩
  rw [hF', evalHom_single]
  simp

/-- The projection `(ℂ^×)^{r+N} → (ℂ^×)^r` onto the first `r` coordinates, as a monomial
map (`η = 1`). -/
def projMat (r N : ℕ) : Matrix (Fin r) (Fin (r + N)) ℤ :=
  Matrix.of fun j k => if k = Fin.castAdd N j then 1 else 0

theorem evalHom_pullback_projMat {r N : ℕ} (y : Fin (r + N) → ℂˣ) (F : MvLaurent r) :
    evalHom y (pullback 1 (projMat r N) F) = evalHom (fun j => y (Fin.castAdd N j)) F := by
  rw [evalHom_pullback]
  congr 2
  funext j
  simp only [monomialMap, projMat, Pi.one_apply, one_mul, Matrix.of_apply]
  rw [Finset.prod_eq_single (Fin.castAdd N j) (fun k _ hk => by simp [hk]) (by simp)]
  simp

end MvLaurent

/-- An exceptional family is not isotrivial: some coefficient is non-constant. -/
theorem nonConst_of_isExceptional {d r : ℕ} {K : IntermediateField ℚ ℂ}
    {a : Fin (d - 1) → AddMonoidAlgebra K (Fin r → ℤ)} {T : Set (Fin r → ℂˣ)}
    (hEx : IsExceptional d K r a T) :
    ∃ i, MvLaurent.NonConst (AddMonoidAlgebra.mapRingHom (Fin r → ℤ) K.val.toRingHom (a i)) := by
  by_contra h
  push Not at h
  apply hEx.1
  refine Set.Subsingleton.finite fun t ht t' ht' => hEx.2.2.2 ht ht' ?_
  funext i
  have h1 := MvLaurent.evalHom_of_not_nonConst (h i) t
  have h2 := MvLaurent.evalHom_of_not_nonConst (h i) t'
  exact h1.trans h2.symm

/-- **Lemma 9.** There are no exceptional families. -/
theorem not_isExceptional (hIB : IngramBound) (hDZ : DvornicichZannier) (hL : Laurent)
    (hSA : SuperAttracting) (d : ℕ) (hd : 2 ≤ d) (K : IntermediateField ℚ ℂ)
    (hK : FiniteDimensional ℚ K) (r : ℕ) (a : Fin (d - 1) → AddMonoidAlgebra K (Fin r → ℤ))
    (T : Set (Fin r → ℂˣ)) : ¬ IsExceptional d K r a T := by
  classical
  induction r using Nat.strong_induction_on generalizing K with
  | _ r ih =>
  intro hEx
  let ι := AddMonoidAlgebra.mapRingHom (Fin r → ℤ) K.val.toRingHom
  obtain ⟨D, hD, E, -, N, hrep⟩ := exists_W_representations hIB hDZ hd K hK
  have : IsIntegrallyClosed (AddMonoidAlgebra K (Fin r → ℤ)) := isIntegrallyClosed_mvLaurent K r
  obtain ⟨A, hAm, hAdvd, hWne, x, q, hq, hord⟩ :=
    exists_highOrderResultant hSA ι hd a (nonConst_of_isExceptional hEx)
  set W := IngramMello.W A (monicCentred d a) (q * (N + 1)) (q * N) with hWdef
  -- Step 1: representations padded to exactly `N` terms.
  have hrep' : ∀ t ∈ T, ∃ (c : Fin N → ↥(insert (0 : ℂ) E)) (ξ : Fin N → ℂˣ),
      (∀ i, IsRootOfUnityC (ξ i : ℂ)) ∧
      (D : ℂ) ^ (d - 1) * MvLaurent.evalOver K t W = ∑ i, (c i : ℂ) * ξ i := by
    intro t ht
    obtain ⟨n, c, ξ, hn, hc, hξ, hsum⟩ := hrep r a A hAm hAdvd t (hEx.2.1 t ht)
      (hEx.2.2.1 t ht) (q * (N + 1)) (q * N)
    have hξ0 : ∀ i, ξ i ≠ 0 := fun i h0 => by
      obtain ⟨m, hm, hm1⟩ := hξ i
      rw [h0, zero_pow hm.ne'] at hm1
      exact zero_ne_one hm1
    refine ⟨fun k => if h : (k : ℕ) < n then ⟨c ⟨k, h⟩, Finset.mem_insert_of_mem (hc _)⟩
        else ⟨0, Finset.mem_insert_self _ _⟩,
      fun k => if h : (k : ℕ) < n then Units.mk0 (ξ ⟨k, h⟩) (hξ0 _) else 1, fun k => ?_, ?_⟩
    · by_cases h : (k : ℕ) < n
      · simp only [h, dite_true, Units.val_mk0]
        exact hξ _
      · simp only [h, dite_false, Units.val_one]
        exact ⟨1, one_pos, one_pow 1⟩
    · rw [hsum, sum_fin_pad hn]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : (k : ℕ) < n <;> simp [h]
  have : Nonempty ↥(insert (0 : ℂ) E) := ⟨⟨0, Finset.mem_insert_self _ _⟩⟩
  choose! cf ξf hξf hsumf using hrep'
  -- Step 2: pigeonhole on the coefficient vector.
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin N → ↥(insert (0 : ℂ) E), {t | t ∈ T ∧ cf t = c₀}.Infinite := by
    by_contra hfin
    push Not at hfin
    apply hEx.1
    refine (Set.finite_iUnion fun c₀ => hfin c₀).subset fun t ht => ?_
    exact Set.mem_iUnion.2 ⟨cf t, ht, rfl⟩
  set T' := {t | t ∈ T ∧ cf t = c₀} with hT'
  -- Step 3: adjoin the roots of unity as new coordinates, and apply Laurent.
  let lift : (Fin r → ℂˣ) → Fin (r + N) → ℂ := fun t =>
    Fin.append (fun j => (t j : ℂ)) (fun i => (ξf t i : ℂ))
  have hlift_inj : Function.Injective lift := fun t t' h => funext fun j =>
    Units.ext (by simpa [lift] using congrFun h (Fin.castAdd N j))
  have hTt_tor : ∀ p ∈ lift '' T', ∀ j, IsRootOfUnityC (p j) := by
    rintro _ ⟨t, ht, rfl⟩ j
    refine Fin.addCases (fun j => ?_) (fun i => ?_) j
    · simpa [lift] using hEx.2.1 t ht.1 j
    · simpa [lift] using hξf t ht.1 i
  obtain ⟨s, η, B, hs, hη, hB, hdense⟩ :=
    hL (r + N) (lift '' T') hTt_tor (hc₀.image hlift_inj.injOn)
  have hη0 : ∀ j, η j ≠ 0 := fun j h0 => by
    obtain ⟨m, hm, hm1⟩ := hη j
    rw [h0, zero_pow hm.ne'] at hm1
    exact zero_ne_one hm1
  let ηu : Fin (r + N) → ℂˣ := fun j => Units.mk0 (η j) (hη0 j)
  -- Step 4: the relation `D^(d-1) W(u) = ∑ c₀ᵢ vᵢ` holds on the coset.
  let G : MvLaurent (r + N) :=
    MvLaurent.pullback 1 (MvLaurent.projMat r N)
        (algebraMap ℂ (MvLaurent r) ((D : ℂ) ^ (d - 1)) * ι W) -
      ∑ i, single (Pi.single (Fin.natAdd r i) 1) ((c₀ i : ℂ))
  have hGeval : ∀ p : Fin (r + N) → ℂ, (∀ j, p j ≠ 0) → MvLaurent.eval G p =
      (D : ℂ) ^ (d - 1) * MvLaurent.eval (ι W) (fun j => p (Fin.castAdd N j)) -
        ∑ i, (c₀ i : ℂ) * p (Fin.natAdd r i) := by
    intro p hp
    rw [MvLaurent.eval_eq_evalHom G p hp]
    simp only [G, map_sub, map_sum, MvLaurent.evalHom_pullback_projMat, map_mul,
      AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, MvLaurent.evalHom_single]
    congr 1
    · rw [MvLaurent.evalHom_apply]
      rfl
    · refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      rw [Finset.prod_eq_single (Fin.natAdd r i) (fun k _ hk => by simp [hk]) (by simp)]
      simp
  have hcoset : ∀ w : Fin s → ℂˣ,
      (D : ℂ) ^ (d - 1) * MvLaurent.eval (ι W)
          (fun j => (MvLaurent.monomialMap ηu B w (Fin.castAdd N j) : ℂ)) =
        ∑ i, (c₀ i : ℂ) * (MvLaurent.monomialMap ηu B w (Fin.natAdd r i) : ℂ) := by
    have hvan : ∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → MvLaurent.eval G (cosetPt η B w) = 0 := by
      refine hdense G fun w hw hmem => ?_
      obtain ⟨t, ht, hte⟩ := hmem
      rw [hGeval _ (cosetPt_ne_zero hη0 B hw), ← hte, sub_eq_zero]
      have h1 := hsumf t ht.1
      rw [ht.2] at h1
      simp only [lift, Fin.append_left, Fin.append_right]
      rw [← MvLaurent.evalHom_apply]
      exact h1
    intro w
    have hp := hvan (fun k => (w k : ℂ)) (fun k => (w k).ne_zero)
    rw [hGeval _ (cosetPt_ne_zero hη0 B fun k => (w k).ne_zero), sub_eq_zero] at hp
    have hc := MvLaurent.coe_monomialMap ηu B w
    have hηu : (fun j => (ηu j : ℂ)) = η := funext fun j => Units.val_mk0 _
    rw [hηu] at hc
    rw [← hc] at hp
    exact hp
  rcases MvLaurent.exists_rank_factorization (B.submatrix (Fin.castAdd N) id) with
    hdom | ⟨r', hr', B₁, B₂, hB₁, hfac⟩
  · -- Dominant projection: Hajós.
    have hιW : ι W ≠ 0 := by
      have hW0 : W ≠ 0 := hWne _ _ (by nlinarith)
      obtain ⟨e, he⟩ : ∃ e, W.coeff e ≠ 0 := by
        by_contra h'
        push Not at h'
        exact hW0 (AddMonoidAlgebra.ext (Finsupp.ext h'))
      intro h0
      apply he
      have := congrArg (fun F : MvLaurent r => F.coeff e) h0
      simp only [ι, AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_zero,
        Finsupp.coe_zero, Pi.zero_apply] at this
      exact Subtype.ext this
    refine MvLaurent.false_of_dominant_coset (algebraMap ℂ (MvLaurent r) ((D : ℂ) ^ (d - 1)) * ι W)
      ?_ x (Ideal.mul_mem_left _ _ (hord N)) (fun i => (c₀ i : ℂ)) ηu B hdom fun w => ?_
    · refine mul_ne_zero ?_ hιW
      rw [map_ne_zero_iff _ (algebraMap ℂ (MvLaurent r)).injective]
      exact pow_ne_zero _ (by exact_mod_cast hD.ne')
    · rw [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
        MvLaurent.evalHom_apply]
      exact hcoset w
  · -- Projection into a smaller torsion coset: descend.
    let T₀ : Set (Fin r → ℂˣ) := {t | t ∈ T' ∧ lift t ∈ cosetSet η B}
    have hT₀inf : T₀.Infinite := by
      have hinf := infinite_of_laurent_dense hs hη0 hB (lift '' T') hdense
      refine Set.Infinite.of_image lift (hinf.mono ?_)
      rintro _ ⟨⟨t, ht, rfl⟩, hc⟩
      exact ⟨t, ⟨ht, hc⟩, rfl⟩
    have hT₀B : ∀ t ∈ T₀, ∃ w,
        MvLaurent.monomialMap (fun j => ηu (Fin.castAdd N j)) B₁ w = t := by
      rintro t ⟨-, w, hw, hwe⟩
      let wu : Fin s → ℂˣ := fun k => Units.mk0 (w k) (hw k)
      refine ⟨MvLaurent.monomialMap 1 B₂ wu, ?_⟩
      rw [← MvLaurent.monomialMap_mul, ← hfac]
      funext j
      apply Units.ext
      have h1 := congrFun (MvLaurent.coe_monomialMap ηu B wu) (Fin.castAdd N j)
      have h2 := congrFun hwe (Fin.castAdd N j)
      simp only [lift, Fin.append_left] at h2
      change (MvLaurent.monomialMap ηu B wu (Fin.castAdd N j) : ℂ) = t j
      rw [h1, ← h2]
      simp [ηu, wu]
    have : FiniteDimensional ℚ K := hK
    obtain ⟨L, hLf, a', T'', hEx''⟩ := isExceptional_descent hEx
      (fun j => ηu (Fin.castAdd N j)) (fun j => by simpa [ηu] using hη (Fin.castAdd N j))
      B₁ hB₁ T₀ (fun t ht => ht.1.1) hT₀inf hT₀B
    exact ih r' hr' L hLf a' T'' hEx''

end IngramMello
