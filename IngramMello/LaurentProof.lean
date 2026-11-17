import IngramMello.TorsionFiber
import IngramMello.TorsionCoeffDescent

/-!
# Laurent's theorem for torsion points (Lemma 2 of the paper)

`laurent_of_mann : Laurent`. This is the torsion case of Laurent's theorem (M. Laurent,
*Équations diophantiennes exponentielles*, Invent. Math. 78 (1984), no. 2, 299–327); the proof
here goes through Mann's theorem on vanishing sums of roots of unity (`Mann.lean`) and does not
use Laurent's theorem itself. Induction on the torus dimension: either the infinite torsion
set `T` is Zariski dense in `(ℂ^×)^r` (then `C = (ℂ^×)^r`), or some nonzero Laurent
polynomial vanishes on it; by coefficient descent a rational one does
(`exists_rational_equation_of_torsion`), Mann's theorem puts infinitely many points of `T`
on a character fiber (`exists_character_of_infinite`), the fiber is covered by finitely many
monomial parametrizations of dimension `r - 1` (`exists_fiber_cover`), and the induction
hypothesis applies to the lifted set. Compositions of monomial parametrizations are
again of the required form.
-/

namespace IngramMello

open Finset MvLaurent

variable {r s t : ℕ}

/-! ### Helper identities -/

theorem cosetPt_one_one (w : Fin r → ℂ) :
    cosetPt (fun _ : Fin r => (1 : ℂ)) (1 : Matrix (Fin r) (Fin r) ℤ) w = w := by
  funext j
  simp only [cosetPt, Matrix.one_apply, one_mul]
  rw [Finset.prod_eq_single j]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem MvLaurent.eval_zero (u : Fin r → ℂ) : MvLaurent.eval (0 : MvLaurent r) u = 0 := by
  simp [MvLaurent.eval]

/-- `η (η' w^{B'})^{B} = (η η'^B) w^{B B'}` in units form. -/
theorem MvLaurent.monomialMap_monomialMap (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin t) ℤ)
    (η' : Fin t → ℂˣ) (B' : Matrix (Fin t) (Fin s) ℤ) (w : Fin s → ℂˣ) :
    monomialMap η B (monomialMap η' B' w) = monomialMap (monomialMap η B η') (B * B') w := by
  have h := congrFun (MvLaurent.monomialMap_one_comp B' B w)
  funext j
  have hj := h j
  simp only [monomialMap, Pi.one_apply, one_mul] at hj ⊢
  rw [← hj, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [mul_zpow]

/-- Composition of two coset parametrizations, for points with nonzero coordinates. -/
theorem cosetPt_cosetPt {η : Fin r → ℂ} (hη : ∀ j, η j ≠ 0) (B : Matrix (Fin r) (Fin t) ℤ)
    {η' : Fin t → ℂ} (hη' : ∀ k, η' k ≠ 0) (B' : Matrix (Fin t) (Fin s) ℤ)
    {u : Fin s → ℂ} (hu : ∀ l, u l ≠ 0) :
    cosetPt (cosetPt η B η') (B * B') u = cosetPt η B (cosetPt η' B' u) := by
  set ηu : Fin r → ℂˣ := fun j => Units.mk0 (η j) (hη j) with hηu
  set η'u : Fin t → ℂˣ := fun k => Units.mk0 (η' k) (hη' k) with hη'u
  set uu : Fin s → ℂˣ := fun l => Units.mk0 (u l) (hu l) with huu
  have h1 : (fun j => (ηu j : ℂ)) = η := by funext j; simp [hηu]
  have h2 : (fun k => (η'u k : ℂ)) = η' := by funext k; simp [hη'u]
  have h3 : (fun l => (uu l : ℂ)) = u := by funext l; simp [huu]
  rw [← h1, ← h2, ← h3, ← MvLaurent.coe_monomialMap, ← MvLaurent.coe_monomialMap,
    ← MvLaurent.coe_monomialMap, ← MvLaurent.coe_monomialMap,
    MvLaurent.monomialMap_monomialMap]

/-- Evaluation of a pullback at a point with nonzero coordinates. -/
theorem MvLaurent.eval_pullback_coe (η : Fin r → ℂˣ) (B : Matrix (Fin r) (Fin s) ℤ)
    (z : Fin s → ℂˣ) (P : MvLaurent r) :
    MvLaurent.eval (pullback η B P) (fun k => (z k : ℂ)) =
      MvLaurent.eval P (cosetPt (fun j => (η j : ℂ)) B (fun k => (z k : ℂ))) := by
  rw [← evalHom_apply, evalHom_pullback, evalHom_apply, coe_monomialMap]

/-- A rational Laurent polynomial evaluated at a torus point is a rational combination
of characters. -/
theorem MvLaurent.eval_mapRingHom_rat (Q : AddMonoidAlgebra ℚ (Fin r → ℤ)) (x : Fin r → ℂˣ) :
    MvLaurent.eval (AddMonoidAlgebra.mapRingHom _ (algebraMap ℚ ℂ) Q) (fun j => (x j : ℂ)) =
      ∑ e ∈ Q.coeff.support, (Q.coeff e : ℂ) * (charPow x e : ℂ) := by
  simp only [MvLaurent.eval, AddMonoidAlgebra.coe_mapRingHom, AddMonoidAlgebra.coeff_map,
    coe_charPow]
  rw [Finsupp.sum_mapRange_index (by simp)]
  rfl

/-! ### The induction -/

/-- The statement `Laurent`, for a fixed torus dimension `r`. -/
theorem laurent_dim (r : ℕ) : ∀ T : Set (Fin r → ℂ), (∀ t ∈ T, ∀ j, IsRootOfUnityC (t j)) →
    T.Infinite →
    ∃ (s : ℕ) (η : Fin r → ℂ) (B : Matrix (Fin r) (Fin s) ℤ),
      0 < s ∧ (∀ j, IsRootOfUnityC (η j)) ∧ Function.Injective B.mulVec ∧
      ∀ P : MvLaurent r,
        (∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → cosetPt η B w ∈ T →
          MvLaurent.eval P (cosetPt η B w) = 0) →
        ∀ w : Fin s → ℂ, (∀ k, w k ≠ 0) → MvLaurent.eval P (cosetPt η B w) = 0 := by
  classical
  induction r with
  | zero =>
    intro T _ hinf
    exact absurd (Set.toFinite T) hinf
  | succ r' ih =>
    intro T hT hinf
    have hne : ∀ t ∈ T, ∀ j, t j ≠ 0 := fun t ht j => (hT t ht j).ne_zero
    by_cases hdense : ∀ P : MvLaurent (r' + 1), (∀ t ∈ T, MvLaurent.eval P t = 0) → P = 0
    · -- dense case: the whole torus
      refine ⟨r' + 1, fun _ => 1, 1, Nat.succ_pos _, fun _ => ⟨1, one_pos, one_pow 1⟩, ?_, ?_⟩
      · intro u u' h
        simpa [Matrix.one_mulVec] using h
      · intro P hP w _
        have hP' : ∀ t ∈ T, MvLaurent.eval P t = 0 := fun t ht => by
          have := hP t (hne t ht) (by rw [cosetPt_one_one]; exact ht)
          rwa [cosetPt_one_one] at this
        rw [hdense P hP', MvLaurent.eval_zero]
    · push Not at hdense
      obtain ⟨P, hPz, hP0⟩ := hdense
      obtain ⟨Q, hQ0, hQz⟩ := MvLaurent.exists_rational_equation_of_torsion hT hP0 hPz
      -- pass to units
      set Tu : Set (Fin (r' + 1) → ℂˣ) := {x | (fun j => (x j : ℂ)) ∈ T} with hTu
      have hTu_inf : Tu.Infinite := by
        intro hfin
        apply hinf
        refine Set.Finite.subset (hfin.image fun x : Fin (r' + 1) → ℂˣ => fun j => (x j : ℂ)) ?_
        intro t ht
        refine ⟨fun j => Units.mk0 (t j) (hne t ht j), ?_, ?_⟩
        · change (fun j => ((Units.mk0 (t j) (hne t ht j) : ℂˣ) : ℂ)) ∈ T
          simpa using ht
        · funext j; simp
      have hTu_tor : ∀ x ∈ Tu, ∀ j, IsRootOfUnityC (x j : ℂ) := fun x hx j => hT _ hx j
      have hTu_van : ∀ x ∈ Tu,
          ∑ e ∈ Q.coeff.support, (Q.coeff e : ℂ) * (charPow x e : ℂ) = 0 := fun x hx => by
        rw [← MvLaurent.eval_mapRingHom_rat]; exact hQz _ hx
      have hQsupp : Q.coeff.support.Nonempty :=
        Finsupp.support_nonempty_iff.2 fun h => hQ0 (AddMonoidAlgebra.ext h)
      obtain ⟨v, hv, hTv⟩ := exists_character_of_infinite Q.coeff.support (fun e => Q.coeff e)
        (fun e he => Finsupp.mem_support_iff.1 he) hQsupp Tu hTu_inf hTu_tor hTu_van
      obtain ⟨F, B, hF, hB, hcover⟩ := exists_fiber_cover v hv
      -- pigeonhole over the finitely many `η`
      set good : (Fin (r' + 1) → ℂ) → Set (Fin (r' + 1) → ℂˣ) := fun η =>
        {x ∈ Tu | charPow x v = 1 ∧ ∃ w : Fin r' → ℂ, (∀ k, w k ≠ 0) ∧
          (∀ k, IsRootOfUnityC (w k)) ∧ cosetPt η B w = fun j => (x j : ℂ)} with hgood
      obtain ⟨η, hηF, hηinf⟩ : ∃ η ∈ F, (good η).Infinite := by
        by_contra hcon
        push Not at hcon
        apply hTv
        refine Set.Finite.subset
          (Set.Finite.biUnion (Finset.finite_toSet F) fun η hη => hcon η hη) ?_
        intro x hx
        obtain ⟨η, hη, w, hw0, hwt, hcos⟩ := hcover x (hTu_tor x hx.1) hx.2
        rw [Set.mem_iUnion₂]
        exact ⟨η, hη, hx.1, hx.2, w, hw0, hwt, hcos⟩
      have hη : ∀ j, IsRootOfUnityC (η j) := hF η hηF
      have hη0 : ∀ j, η j ≠ 0 := fun j => (hη j).ne_zero
      -- choose one lift per point
      have hlift : ∀ x ∈ good η, ∃ w : Fin r' → ℂ, (∀ k, w k ≠ 0) ∧
          (∀ k, IsRootOfUnityC (w k)) ∧ cosetPt η B w = fun j => (x j : ℂ) :=
        fun x hx => hx.2.2
      choose! w hw using hlift
      set T' : Set (Fin r' → ℂ) := w '' good η with hT'
      have hinjw : Set.InjOn w (good η) := by
        intro x hx y hy hxy
        have hx' := (hw x hx).2.2
        have hy' := (hw y hy).2.2
        rw [hxy, hy'] at hx'
        funext j
        exact Units.ext (congrFun hx' j).symm
      have hT'inf : T'.Infinite := (Set.infinite_image_iff hinjw).2 hηinf
      have hT'tor : ∀ t ∈ T', ∀ k, IsRootOfUnityC (t k) := by
        rintro t ⟨x, hx, rfl⟩ k
        exact (hw x hx).2.1 k
      obtain ⟨s, η', B', hs, hη', hB', hdens'⟩ := ih T' hT'tor hT'inf
      have hη'0 : ∀ k, η' k ≠ 0 := fun k => (hη' k).ne_zero
      refine ⟨s, cosetPt η B η', B * B', hs, ?_, ?_, ?_⟩
      · intro j
        exact (hη j).mul (IsRootOfUnityC.finset_prod _ _ fun k _ => (hη' k).zpow _)
      · intro u u' h
        apply hB'
        apply hB
        rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      · intro P hP u hu
        set ηu : Fin (r' + 1) → ℂˣ := fun j => Units.mk0 (η j) (hη0 j) with hηu
        have hηuc : (fun j => (ηu j : ℂ)) = η := by funext j; simp [hηu]
        set Pb := pullback ηu B P with hPb
        have hPb_eval : ∀ z : Fin r' → ℂ, (∀ k, z k ≠ 0) →
            MvLaurent.eval Pb z = MvLaurent.eval P (cosetPt η B z) := by
          intro z hz
          set zu : Fin r' → ℂˣ := fun k => Units.mk0 (z k) (hz k) with hzu
          have hzuc : (fun k => (zu k : ℂ)) = z := by funext k; simp [hzu]
          rw [← hzuc, ← hηuc, hPb, MvLaurent.eval_pullback_coe]
        have hcomp : ∀ z : Fin s → ℂ, (∀ k, z k ≠ 0) →
            cosetPt (cosetPt η B η') (B * B') z = cosetPt η B (cosetPt η' B' z) :=
          fun z hz => cosetPt_cosetPt hη0 B hη'0 B' hz
        have h1 : ∀ z : Fin s → ℂ, (∀ k, z k ≠ 0) → cosetPt η' B' z ∈ T' →
            MvLaurent.eval Pb (cosetPt η' B' z) = 0 := by
          intro z hz hmem
          obtain ⟨x, hx, hxz⟩ := hmem
          have hmemT : cosetPt (cosetPt η B η') (B * B') z ∈ T := by
            rw [hcomp z hz, ← hxz, (hw x hx).2.2]
            exact hx.1
          have := hP z hz hmemT
          rw [hcomp z hz] at this
          rw [hPb_eval _ (cosetPt_ne_zero hη'0 B' hz)]
          exact this
        have := hdens' Pb h1 u hu
        rwa [hPb_eval _ (cosetPt_ne_zero hη'0 B' hu), ← hcomp u hu] at this

/-- **Laurent's theorem** in the form of `Inputs.lean`, proved from Mann's theorem. -/
theorem laurent_of_mann : Laurent := laurent_dim

end IngramMello
