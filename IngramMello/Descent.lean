import IngramMello.Resultants
import IngramMello.Torsion

/-!
# Bounded resultants and exceptional families

The bounded-house estimate for the resultants `W_{ℓ,j}` used in the proof of Lemma 9,
including the uniform denominator when the monic factor has degree smaller than `d - 1`,
and the definition of an exceptional family (Section 6 of the paper).
-/

namespace IngramMello

open Polynomial

/-- Conjugates can be computed using embeddings of any algebraic field
containing the element. This lets us bound products using a common embedding. -/
theorem houseLE_iff_embeddings {E : Type*} [Field E] [Algebra ℚ E]
    [Algebra.IsAlgebraic ℚ E] (φ : E →ₐ[ℚ] ℂ) (x : E) (M : ℝ) :
    HouseLE (φ x) M ↔ ∀ σ : E →ₐ[ℚ] ℂ, ‖σ x‖ ≤ M := by
  have hp : minpoly ℚ (φ x) = minpoly ℚ x := minpoly.algHom_eq φ φ.injective x
  constructor
  · intro h σ
    apply h
    rw [hp, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · intro h z hz
    rw [hp] at hz
    obtain ⟨σ, rfl⟩ := IntermediateField.exists_algHom_of_splits_of_aeval
      (fun y : E => ⟨Algebra.IsIntegral.isIntegral y, IsAlgClosed.splits _⟩) hz
    exact h σ

/-- The house is submultiplicative for algebraic complex numbers. -/
theorem HouseLE.mul {x y : ℂ} {M N : ℝ}
    (hx : HouseLE x M) (hy : HouseLE y N)
    (hxi : IsIntegral ℚ x) (hyi : IsIntegral ℚ y) : HouseLE (x * y) (M * N) := by
  let E := algebraicClosure ℚ ℂ
  let x' : E := ⟨x, hxi⟩
  let y' : E := ⟨y, hyi⟩
  apply (houseLE_iff_embeddings E.val (x' * y') (M * N)).mpr
  intro σ
  rw [map_mul, norm_mul]
  exact mul_le_mul ((houseLE_iff_embeddings E.val x' M).mp hx σ)
    ((houseLE_iff_embeddings E.val y' N).mp hy σ) (norm_nonneg _)
    ((norm_nonneg x).trans (hx x (minpoly.aeval ℚ x)))

theorem IsBoundedAlgInt.mul {x y : ℂ} {M N : ℝ}
    (hx : IsBoundedAlgInt M x) (hy : IsBoundedAlgInt N y) :
    IsBoundedAlgInt (M * N) (x * y) :=
  ⟨hx.1.mul hy.1, hx.2.mul hy.2 hx.1.tower_top hy.1.tower_top⟩

theorem isBoundedAlgInt_natCast (n : ℕ) : IsBoundedAlgInt (n : ℝ) (n : ℂ) := by
  refine ⟨isIntegral_natCast n, ?_⟩
  apply (houseLE_iff_embeddings (algebraicClosure ℚ ℂ).val
    (n : algebraicClosure ℚ ℂ) (n : ℝ)).mpr
  intro σ
  simp

theorem IsBoundedAlgInt.mono {x : ℂ} {M N : ℝ}
    (hx : IsBoundedAlgInt M x) (h : M ≤ N) : IsBoundedAlgInt N x :=
  ⟨hx.1, fun z hz => (hx.2 z hz).trans h⟩

theorem IsBoundedAlgInt.pow {x : ℂ} {M : ℝ}
    (hx : IsBoundedAlgInt M x) (n : ℕ) : IsBoundedAlgInt (M ^ n) (x ^ n) := by
  induction n with
  | zero => simpa using isBoundedAlgInt_natCast 1
  | succ n ih => simpa [pow_succ] using ih.mul hx

/-- Products retain multiplicities, as required by the resultant formula. -/
theorem isBoundedAlgInt_multiset_prod (s : Multiset ℂ) {M : ℝ}
    (h : ∀ x ∈ s, IsBoundedAlgInt M x) : IsBoundedAlgInt (M ^ s.card) s.prod := by
  induction s using Multiset.induction_on with
  | empty => simpa using isBoundedAlgInt_natCast 1
  | cons x s ih =>
    simpa [pow_succ, mul_comm] using
      (h x (Multiset.mem_cons_self x s)).mul (ih (fun y hy => h y (Multiset.mem_cons_of_mem hy)))

/-- Clear a fixed denominator for a product of at most `n` factors. -/
theorem bounded_scaled_prod (s : Multiset ℂ) {D n : ℕ} {M : ℝ}
    (hcard : s.card ≤ n) (h : ∀ x ∈ s, IsBoundedAlgInt M ((D : ℂ) * x)) :
    IsBoundedAlgInt ((D : ℝ) ^ (n - s.card) * M ^ s.card)
      ((D : ℂ) ^ n * s.prod) := by
  have hp := isBoundedAlgInt_multiset_prod (s.map fun x => (D : ℂ) * x)
    (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.mp hx
      exact h y hy)
  have heq : (s.map fun x => (D : ℂ) * x).prod = (D : ℂ) ^ s.card * s.prod := by
    clear hcard h hp
    induction s using Multiset.induction_on with
    | empty => simp
    | cons x s ih => simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons,
        ih, pow_succ]; ring
  rw [heq, Multiset.card_map] at hp
  have ht := ((isBoundedAlgInt_natCast D).pow (n - s.card)).mul hp
  simpa only [← mul_assoc, ← pow_add, Nat.sub_add_cancel hcard] using ht

/-- A bound independent of the number of factors, including the empty product. -/
theorem scaled_prod_bound_uniform {D n k : ℕ} {M : ℝ} (hk : k ≤ n) (hM : 0 ≤ M) :
    (D : ℝ) ^ (n - k) * M ^ k ≤ (max (D : ℝ) (max 1 M)) ^ n := by
  let B := max (D : ℝ) (max 1 M)
  have hB : 0 ≤ B := (Nat.cast_nonneg D).trans (le_max_left _ _)
  calc
    (D : ℝ) ^ (n - k) * M ^ k ≤ B ^ (n - k) * B ^ k := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Nat.cast_nonneg D) (le_max_left _ _) _
      · exact pow_le_pow_left₀ hM ((le_max_right 1 M).trans (le_max_right _ _)) _
      · positivity
      · positivity
    _ = B ^ n := by rw [← pow_add, Nat.sub_add_cancel hk]

/-- A monic divisor of the derivative of a degree `d` monic centred polynomial
has degree at most `d - 1`. -/
theorem natDegree_le_of_dvd_derivative_monicCentred {d : ℕ} (hd : 2 ≤ d)
    (a : Fin (d - 1) → ℂ) {A : ℂ[X]} (hdiv : A ∣ derivative (monicCentred d a)) :
    A.natDegree ≤ d - 1 := by
  obtain ⟨g, hgm, hgdeg, hfg⟩ := exists_derivative_monicCentred hd a
  have hd0 : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [hfg] at hdiv
  have hdeg : (C (d : ℂ) * g).natDegree = d - 1 := by
    rw [natDegree_C_mul hd0, hgdeg]
  exact hdeg ▸ natDegree_le_of_dvd hdiv (mul_ne_zero (C_ne_zero.mpr hd0) hgm.ne_zero)

/-- **Precise denominator estimate** for `W`. The exponent of `M` is the
actual degree of the monic factor; the unused denominator powers remain. -/
theorem isBoundedAlgInt_W {d D : ℕ} {M : ℝ} (hd : 2 ≤ d)
    (a : Fin (d - 1) → ℂ) {A : ℂ[X]} (hA : A.Monic)
    (hdiv : A ∣ derivative (monicCentred d a))
    (hbound : ∀ c : ℂ, (derivative (monicCentred d a)).IsRoot c → ∀ l j : ℕ,
      IsBoundedAlgInt M ((D : ℂ) *
        ((fun z => (monicCentred d a).eval z)^[l] c -
          (fun z => (monicCentred d a).eval z)^[j] c))) (l j : ℕ) :
    IsBoundedAlgInt ((D : ℝ) ^ (d - 1 - A.natDegree) * M ^ A.natDegree)
      ((D : ℂ) ^ (d - 1) * W A (monicCentred d a) l j) := by
  let diff := fun c => (fun z => (monicCentred d a).eval z)^[l] c -
    (fun z => (monicCentred d a).eval z)^[j] c
  have hcard : (A.roots.map diff).card = A.natDegree := by
    rw [Multiset.card_map, ← (IsAlgClosed.splits A).natDegree_eq_card_roots]
  have hprod : (A.roots.map diff).prod = W A (monicCentred d a) l j := by
    simpa using (ev_W hA (monicCentred d a) (RingHom.id ℂ) l j).symm
  have h := bounded_scaled_prod (A.roots.map diff)
    (hcard ▸ natDegree_le_of_dvd_derivative_monicCentred hd a hdiv)
    (D := D) (M := M) (fun x hx => by
      obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.mp hx
      exact hbound c (Polynomial.IsRoot.dvd ((mem_roots hA.ne_zero).mp hc) hdiv) l j)
  rwa [hcard, hprod] at h

/-- **Uniform house bound for `W`** from Proposition 3. The same `D, B`
work for every monic derivative factor and every pair of iterate indices. -/
theorem exists_uniform_W_bound (hIB : IngramBound) {d : ℕ} (hd : 2 ≤ d) :
    ∃ D : ℕ, 0 < D ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ a : Fin (d - 1) → ℂ, (∀ i, IsAlgebraic ℚ (a i)) →
        IsPCF (monicCentred d a) → ∀ A : ℂ[X], A.Monic →
        A ∣ derivative (monicCentred d a) → ∀ l j : ℕ,
          IsBoundedAlgInt B ((D : ℂ) ^ (d - 1) * W A (monicCentred d a) l j) := by
  obtain ⟨D, hD, M, h⟩ := hIB d hd
  refine ⟨D, hD, (max (D : ℝ) (max 1 (max 0 M))) ^ (d - 1), by positivity, ?_⟩
  intro a ha hpcf A hA hdiv l j
  have hb := (h a ha hpcf).2
  have hb' : ∀ c : ℂ, (derivative (monicCentred d a)).IsRoot c → ∀ l j : ℕ,
      IsBoundedAlgInt (max 0 M) ((D : ℂ) *
        ((fun z => (monicCentred d a).eval z)^[l] c -
          (fun z => (monicCentred d a).eval z)^[j] c)) :=
    fun c hc l j => (hb c hc l j).mono (le_max_right _ _)
  exact (isBoundedAlgInt_W hd a hA hdiv hb' l j).mono
    (scaled_prod_bound_uniform (natDegree_le_of_dvd_derivative_monicCentred hd a hdiv)
      (le_max_left 0 M))

/-- Evaluation stays in an intermediate field containing the coefficients
and the coordinates; integer powers cause no problem in a field. -/
theorem MvLaurent.eval_mem_intermediateField {r : ℕ} (F : MvLaurent r)
    (L : IntermediateField ℚ ℂ) (x : Fin r → ℂ)
    (hF : ∀ e, F.coeff e ∈ L) (hx : ∀ i, x i ∈ L) : MvLaurent.eval F x ∈ L := by
  classical
  apply L.sum_mem
  intro e _
  exact L.mul_mem (hF e) (L.prod_mem fun i _ => L.toSubfield.zpow_mem (hx i) _)

theorem mem_Kcyc_of_mem (K : IntermediateField ℚ ℂ) {x : ℂ} (hx : x ∈ K) :
    x ∈ Kcyc K := (le_sup_left : K ≤ Kcyc K) hx

theorem IsRootOfUnityC.mem_Kcyc {x : ℂ} (hx : IsRootOfUnityC x)
    (K : IntermediateField ℚ ℂ) : x ∈ Kcyc K :=
  (le_sup_right : IntermediateField.adjoin ℚ {ζ : ℂ | IsRootOfUnityC ζ} ≤ Kcyc K)
    (IntermediateField.subset_adjoin ℚ _ hx)

/-- Torsion specialization of a Laurent polynomial over `K` belongs to `K^cyc`. -/
theorem MvLaurent.evalHom_map_mem_Kcyc {r : ℕ} (K : IntermediateField ℚ ℂ)
    (F : AddMonoidAlgebra K (Fin r → ℤ)) (x : Fin r → ℂˣ)
    (hx : ∀ i, IsRootOfUnityC (x i : ℂ)) :
    MvLaurent.evalHom x (AddMonoidAlgebra.mapRingHom (Fin r → ℤ) K.val.toRingHom F)
      ∈ Kcyc K := by
  rw [MvLaurent.evalHom_apply]
  apply MvLaurent.eval_mem_intermediateField
  · intro e
    simp only [AddMonoidAlgebra.coeff_mapRingHom]
    exact mem_Kcyc_of_mem K (F.coeff e).property
  · exact fun i => (hx i).mem_Kcyc K

/-- The cyclotomic closure of a number field consists of algebraic numbers. -/
theorem Kcyc_le_algebraicClosure (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K] :
    Kcyc K ≤ algebraicClosure ℚ ℂ := by
  apply sup_le
  · intro x hx
    exact (IsIntegral.of_finite (R := ℚ) (⟨x, hx⟩ : K)).map K.val
  · apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    obtain ⟨n, hn, heq⟩ := hx
    exact IsIntegral.of_pow hn (heq ▸ isIntegral_one)

theorem isAlgebraic_of_mem_Kcyc (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    {x : ℂ} (hx : x ∈ Kcyc K) : IsAlgebraic ℚ x :=
  (mem_algebraicClosure_iff).mp (Kcyc_le_algebraicClosure K hx)

/-- Evaluate a Laurent polynomial with coefficients in an intermediate field. -/
noncomputable def MvLaurent.evalOver {r : ℕ} (K : IntermediateField ℚ ℂ)
    (x : Fin r → ℂˣ) : AddMonoidAlgebra K (Fin r → ℤ) →+* ℂ :=
  (MvLaurent.evalHom x).toRingHom.comp
    (AddMonoidAlgebra.mapRingHom (Fin r → ℤ) K.val.toRingHom)

theorem MvLaurent.evalOver_mem_Kcyc {r : ℕ} (K : IntermediateField ℚ ℂ)
    (x : Fin r → ℂˣ) (hx : ∀ i, IsRootOfUnityC (x i : ℂ))
    (F : AddMonoidAlgebra K (Fin r → ℤ)) : MvLaurent.evalOver K x F ∈ Kcyc K :=
  MvLaurent.evalHom_map_mem_Kcyc K F x hx

/-- **Torsion specializations of `W`.** Both inputs needed for the
Dvornicich–Zannier theorem hold uniformly in the family, factor, and indices. -/
theorem exists_uniform_W_bound_torsion (hIB : IngramBound) {d : ℕ} (hd : 2 ≤ d) :
    ∃ D : ℕ, 0 < D ∧ ∃ B : ℝ, 0 ≤ B ∧
      ∀ (K : IntermediateField ℚ ℂ), FiniteDimensional ℚ K → ∀ r : ℕ,
      ∀ (a : Fin (d - 1) → AddMonoidAlgebra K (Fin r → ℤ))
        (A : (AddMonoidAlgebra K (Fin r → ℤ))[X]),
      A.Monic → A ∣ derivative (monicCentred d a) →
      ∀ x : Fin r → ℂˣ, (∀ i, IsRootOfUnityC (x i : ℂ)) →
      IsPCF (monicCentred d (fun i => MvLaurent.evalOver K x (a i))) → ∀ l j : ℕ,
        let α := (D : ℂ) ^ (d - 1) * MvLaurent.evalOver K x (W A (monicCentred d a) l j)
        IsBoundedAlgInt B α ∧ α ∈ Kcyc K := by
  obtain ⟨D, hD, B, hB, hb⟩ := exists_uniform_W_bound hIB hd
  refine ⟨D, hD, B, hB, ?_⟩
  intro K hK r a A hA hdiv x hx hpcf l j
  let := hK
  let ev := MvLaurent.evalOver K x
  have ha : ∀ i, IsAlgebraic ℚ (ev (a i)) :=
    fun i => isAlgebraic_of_mem_Kcyc K (MvLaurent.evalOver_mem_Kcyc K x hx (a i))
  have hdiv' : A.map ev ∣ derivative (monicCentred d (fun i => ev (a i))) := by
    rw [← map_monicCentred, derivative_map]
    exact Polynomial.map_dvd ev hdiv
  have hW : ev (W A (monicCentred d a) l j) =
      W (A.map ev) (monicCentred d (fun i => ev (a i))) l j := by
    rw [W, resM_map hA, Polynomial.map_sub, map_P, map_P, map_monicCentred]
    rfl
  constructor
  · change IsBoundedAlgInt B ((D : ℂ) ^ (d - 1) * ev (W A (monicCentred d a) l j))
    rw [hW]
    exact hb _ ha hpcf _ (hA.map ev) hdiv' l j
  · change (D : ℂ) ^ (d - 1) * ev (W A (monicCentred d a) l j) ∈ Kcyc K
    exact (Kcyc K).mul_mem ((Kcyc K).toSubfield.pow_mem ((Kcyc K).natCast_mem D) (d - 1))
      (MvLaurent.evalOver_mem_Kcyc K x hx _)

/-- **Bounded root-of-unity representations of the resultants** (proof of Lemma 9).
The finite coefficient set and length bound are chosen before the family
and the iterate indices. This permits the later choice `l = q * (N + 1)`. -/
theorem exists_W_representations (hIB : IngramBound) (hDZ : DvornicichZannier)
    {d : ℕ} (hd : 2 ≤ d) (K : IntermediateField ℚ ℂ) (hK : FiniteDimensional ℚ K) :
    ∃ D : ℕ, 0 < D ∧ ∃ E : Finset ℂ, (∀ e ∈ E, e ∈ K) ∧ ∃ N : ℕ,
      ∀ r : ℕ, ∀ (a : Fin (d - 1) → AddMonoidAlgebra K (Fin r → ℤ))
        (A : (AddMonoidAlgebra K (Fin r → ℤ))[X]),
      A.Monic → A ∣ derivative (monicCentred d a) →
      ∀ x : Fin r → ℂˣ, (∀ i, IsRootOfUnityC (x i : ℂ)) →
      IsPCF (monicCentred d (fun i => MvLaurent.evalOver K x (a i))) → ∀ l j : ℕ,
        ∃ (n : ℕ) (c ξ : Fin n → ℂ), n ≤ N ∧ (∀ i, c i ∈ E) ∧
          (∀ i, IsRootOfUnityC (ξ i)) ∧
          (D : ℂ) ^ (d - 1) * MvLaurent.evalOver K x (W A (monicCentred d a) l j) =
            ∑ i, c i * ξ i := by
  obtain ⟨D, hD, B, -, hb⟩ := exists_uniform_W_bound_torsion hIB hd
  obtain ⟨E, hE, N, hN⟩ := hDZ K hK B
  refine ⟨D, hD, E, hE, N, ?_⟩
  intro r a A hA hdiv x hx hpcf l j
  obtain ⟨hbnd, hmem⟩ := hb K hK r a A hA hdiv x hx hpcf l j
  exact hN _ hmem hbnd.1 hbnd.2

/-- An **exceptional family of dimension `r`** over the number field `K` (Section 6 of the paper):
Laurent polynomials `a_{d-2}, …, a_0 ∈ K[u^{±1}]` and an infinite set `T` of torsion
points of `(ℂ^×)^r` at which every specialization is PCF, with pairwise distinct
specializations. The paper's finite extension `K'/K` is just another number field here. -/
def IsExceptional (d : ℕ) (K : IntermediateField ℚ ℂ) (r : ℕ)
    (a : Fin (d - 1) → AddMonoidAlgebra K (Fin r → ℤ)) (T : Set (Fin r → ℂˣ)) : Prop :=
  T.Infinite ∧ (∀ t ∈ T, ∀ k, IsRootOfUnityC (t k : ℂ)) ∧
    (∀ t ∈ T, IsPCF (monicCentred d fun i => MvLaurent.evalOver K t (a i))) ∧
    Set.InjOn (fun t i => MvLaurent.evalOver K t (a i)) T

/-- Evaluation of `c · u_k`. -/
theorem evalOver_single_basis {r : ℕ} (K : IntermediateField ℚ ℂ) (x : Fin r → ℂˣ)
    (k : Fin r) (c : K) :
    MvLaurent.evalOver K x (AddMonoidAlgebra.single (Pi.single k 1) c) = (c : ℂ) * x k := by
  simp [MvLaurent.evalOver, MvLaurent.evalHom_single, Pi.single_apply]

end IngramMello
