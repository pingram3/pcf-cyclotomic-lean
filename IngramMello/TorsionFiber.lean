import IngramMello.Mann
import IngramMello.Torsion

/-!
# Torsion zeros of a rational Laurent polynomial lie on character fibers

From Mann's theorem: a torsion zero `x` of a rational Laurent polynomial with support `S`
satisfies `x^{N(e-f)} = 1` for two distinct exponents `e, f ∈ S`, `N = (#S)!`. Infinitely
many torsion zeros therefore lie on one character fiber `{x^v = 1}`, `v ≠ 0`, and such a
fiber is covered by finitely many monomial parametrizations of dimension one less
(`exists_fiber_cover`), with no unimodular completion needed.
-/

namespace IngramMello

open Finset

/-! ### Characters of `(ℂ^×)^r` -/

/-- The character `x ↦ x^v = ∏ⱼ xⱼ^{vⱼ}` on `(ℂ^×)^r`. -/
def charPow {r : ℕ} (x : Fin r → ℂˣ) (v : Fin r → ℤ) : ℂˣ := ∏ j, x j ^ v j

variable {r : ℕ}

theorem charPow_add (x : Fin r → ℂˣ) (v w : Fin r → ℤ) :
    charPow x (v + w) = charPow x v * charPow x w := by
  simp [charPow, zpow_add, Finset.prod_mul_distrib]

theorem charPow_neg (x : Fin r → ℂˣ) (v : Fin r → ℤ) : charPow x (-v) = (charPow x v)⁻¹ := by
  simp [charPow, zpow_neg, Finset.prod_inv_distrib]

theorem charPow_sub (x : Fin r → ℂˣ) (v w : Fin r → ℤ) :
    charPow x (v - w) = charPow x v / charPow x w := by
  rw [sub_eq_add_neg, charPow_add, charPow_neg, div_eq_mul_inv]

theorem charPow_zsmul (x : Fin r → ℂˣ) (N : ℤ) (v : Fin r → ℤ) :
    charPow x (N • v) = charPow x v ^ N := by
  simp only [charPow, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [zpow_mul, ← zpow_mul, ← zpow_mul, mul_comm]

theorem coe_charPow (x : Fin r → ℂˣ) (v : Fin r → ℤ) :
    (charPow x v : ℂ) = ∏ j, (x j : ℂ) ^ v j := by
  simp [charPow, Units.val_zpow_eq_zpow_val]

theorem IsRootOfUnityC.finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℂ)
    (h : ∀ i ∈ s, IsRootOfUnityC (f i)) : IsRootOfUnityC (∏ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, one_pos, by simp⟩
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem isRootOfUnityC_charPow (x : Fin r → ℂˣ) (hx : ∀ j, IsRootOfUnityC (x j : ℂ))
    (v : Fin r → ℤ) : IsRootOfUnityC (charPow x v : ℂ) := by
  rw [coe_charPow]
  exact IsRootOfUnityC.finset_prod _ _ fun j _ => (hx j).zpow _

/-! ### Minimal vanishing subsums and Mann -/

/-- A torsion zero of a rational Laurent polynomial with support `S` has two distinct
exponents `e ≠ f` in `S` with `(x^e)^{N} = (x^f)^{N}`, `N = (#S)!`. -/
theorem exists_pair_of_vanishing_sum (S : Finset (Fin r → ℤ)) (q : (Fin r → ℤ) → ℚ)
    (hq : ∀ e ∈ S, q e ≠ 0) (hS : S.Nonempty) (x : Fin r → ℂˣ)
    (hx : ∀ j, IsRootOfUnityC (x j : ℂ))
    (hsum : ∑ e ∈ S, (q e : ℂ) * (charPow x e : ℂ) = 0) :
    ∃ e ∈ S, ∃ f ∈ S, e ≠ f ∧
      charPow x e ^ S.card.factorial = charPow x f ^ S.card.factorial := by
  classical
  -- a vanishing subsum of least cardinality
  set 𝓢 := S.powerset.filter
    (fun S' => S'.Nonempty ∧ ∑ e ∈ S', (q e : ℂ) * (charPow x e : ℂ) = 0) with h𝓢
  have hS𝓢 : S ∈ 𝓢 := by
    rw [h𝓢, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨subset_rfl, hS, hsum⟩
  obtain ⟨S₀, hS₀, hminS₀⟩ := Finset.exists_min_image 𝓢 Finset.card ⟨S, hS𝓢⟩
  rw [h𝓢, Finset.mem_filter, Finset.mem_powerset] at hS₀
  obtain ⟨hS₀S, hS₀ne, hS₀sum⟩ := hS₀
  have hmin : ∀ I ⊆ S₀, I.Nonempty → ∑ e ∈ I, (q e : ℂ) * (charPow x e : ℂ) = 0 → I = S₀ := by
    intro I hI hIne hIsum
    have hI𝓢 : I ∈ 𝓢 := by
      rw [h𝓢, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨hI.trans hS₀S, hIne, hIsum⟩
    exact Finset.eq_of_subset_of_card_le hI (hminS₀ I hI𝓢)
  -- at least two elements
  obtain ⟨e₀, he₀⟩ := hS₀ne
  have hcharne : ∀ e, (charPow x e : ℂ) ≠ 0 := fun e => (charPow x e).ne_zero
  obtain ⟨f₀, hf₀, hf₀e⟩ : ∃ f ∈ S₀, f ≠ e₀ := by
    by_contra h
    push Not at h
    have hsing : S₀ = {e₀} := Finset.eq_singleton_iff_unique_mem.2 ⟨he₀, h⟩
    rw [hsing, Finset.sum_singleton] at hS₀sum
    exact mul_ne_zero (by exact_mod_cast hq e₀ (hS₀S he₀)) (hcharne e₀) hS₀sum
  -- transport to `Fin k` and apply Mann
  set k := S₀.card with hk
  let σ : S₀ ≃ Fin k := S₀.equivFin
  let ζ : Fin k → ℂ := fun i => (charPow x (σ.symm i : Fin r → ℤ) : ℂ)
  let c : Fin k → ℚ := fun i => q (σ.symm i)
  have hζ : ∀ i, IsRootOfUnityC (ζ i) := fun i => isRootOfUnityC_charPow x hx _
  have hsum' : ∑ i, (c i : ℂ) * ζ i = 0 := by
    rw [← hS₀sum, ← Finset.sum_coe_sort S₀]
    exact Equiv.sum_comp σ.symm (fun e : S₀ => (q e : ℂ) * (charPow x e : ℂ))
  have hinj : Function.Injective (fun i : Fin k => (σ.symm i : Fin r → ℤ)) :=
    Subtype.val_injective.comp σ.symm.injective
  have hmin' : ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (c i : ℂ) * ζ i = 0 → I = univ := by
    intro I hI hIsum
    set I' := I.image (fun i : Fin k => (σ.symm i : Fin r → ℤ)) with hI'
    have hI'sub : I' ⊆ S₀ := by
      intro e he
      rw [hI', Finset.mem_image] at he
      obtain ⟨i, _, rfl⟩ := he
      exact (σ.symm i).2
    have hI'sum : ∑ e ∈ I', (q e : ℂ) * (charPow x e : ℂ) = 0 := by
      rw [hI', Finset.sum_image (fun i _ j _ h => hinj h)]
      exact hIsum
    have heq := hmin I' hI'sub (hI.image _) hI'sum
    have hcard : I.card = k := by
      rw [← Finset.card_image_of_injective I hinj, ← hI', heq]
    exact Finset.eq_univ_of_card I (by simpa using hcard)
  have hm := mann c ζ hζ hsum' hmin' (σ ⟨e₀, he₀⟩) (σ ⟨f₀, hf₀⟩)
  simp only [ζ, Equiv.symm_apply_apply] at hm
  refine ⟨e₀, hS₀S he₀, f₀, hS₀S hf₀, hf₀e.symm, ?_⟩
  obtain ⟨t, ht⟩ : k.factorial ∣ S.card.factorial :=
    Nat.factorial_dvd_factorial (Finset.card_le_card hS₀S)
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ht, pow_mul, pow_mul, hm]

/-- Infinitely many torsion zeros of a rational Laurent equation lie on one character
fiber `{x^v = 1}` with `v ≠ 0`. -/
theorem exists_character_of_infinite (S : Finset (Fin r → ℤ)) (q : (Fin r → ℤ) → ℚ)
    (hq : ∀ e ∈ S, q e ≠ 0) (hS : S.Nonempty) (T : Set (Fin r → ℂˣ)) (hT : T.Infinite)
    (htor : ∀ x ∈ T, ∀ j, IsRootOfUnityC (x j : ℂ))
    (hvan : ∀ x ∈ T, ∑ e ∈ S, (q e : ℂ) * (charPow x e : ℂ) = 0) :
    ∃ v : Fin r → ℤ, v ≠ 0 ∧ {x ∈ T | charPow x v = 1}.Infinite := by
  classical
  set N : ℤ := ((S.card.factorial : ℕ) : ℤ) with hN
  by_contra hcon
  push Not at hcon
  apply hT
  set F := (S ×ˢ S).filter (fun p => p.1 ≠ p.2) with hF
  have hsub : T ⊆ ⋃ p ∈ (F : Set ((Fin r → ℤ) × (Fin r → ℤ))),
      {x ∈ T | charPow x (N • (p.1 - p.2)) = 1} := by
    intro x hx
    obtain ⟨e, he, f, hf, hef, h⟩ :=
      exists_pair_of_vanishing_sum S q hq hS x (htor x hx) (hvan x hx)
    rw [Set.mem_iUnion₂]
    refine ⟨(e, f), ?_, hx, ?_⟩
    · rw [Finset.mem_coe, hF, Finset.mem_filter, Finset.mem_product]
      exact ⟨⟨he, hf⟩, hef⟩
    · rw [charPow_zsmul, charPow_sub, div_zpow, hN, zpow_natCast, zpow_natCast, h, div_self']
  refine Set.Finite.subset (Set.Finite.biUnion (Finset.finite_toSet F) fun p hp => hcon _ ?_) hsub
  rw [Finset.mem_coe, hF, Finset.mem_filter] at hp
  exact smul_ne_zero (by rw [hN]; exact_mod_cast (Nat.factorial_ne_zero _)) (sub_ne_zero.2 hp.2)

/-! ### Parametrizing a character fiber -/

/-- The torsion point with `ζ` in coordinate `i₀` and `1` elsewhere. -/
def fiberEta (i₀ : Fin r) (ζ : ℂ) : Fin r → ℂ := fun j => if j = i₀ then ζ else 1

/-- Exponent matrix of the parametrization `w ↦ (w^m on the coordinates ≠ i₀, ζ w^{-v'})`
of the fiber `{x^v = 1}`, where `m = v i₀`. -/
def fiberMat {r' : ℕ} (v : Fin (r' + 1) → ℤ) (i₀ : Fin (r' + 1)) :
    Matrix (Fin (r' + 1)) (Fin r') ℤ :=
  fun j k => if j = i₀ then - v (i₀.succAbove k) else if j = i₀.succAbove k then v i₀ else 0

theorem fiberMat_mulVec_succAbove {r' : ℕ} (v : Fin (r' + 1) → ℤ) (i₀ : Fin (r' + 1))
    (u : Fin r' → ℤ) (k : Fin r') : (fiberMat v i₀).mulVec u (i₀.succAbove k) = v i₀ * u k := by
  simp only [Matrix.mulVec, dotProduct, fiberMat, Fin.succAbove_ne, ite_false,
    Fin.succAbove_right_inj]
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb
    simp [Ne.symm hb]
  · simp

theorem fiberMat_mulVec_injective {r' : ℕ} (v : Fin (r' + 1) → ℤ) (i₀ : Fin (r' + 1))
    (hm : v i₀ ≠ 0) : Function.Injective (fiberMat v i₀).mulVec := by
  intro u u' h
  funext k
  have := congrFun h (i₀.succAbove k)
  rw [fiberMat_mulVec_succAbove, fiberMat_mulVec_succAbove] at this
  exact mul_left_cancel₀ hm this

/-- Every torsion point of the fiber `{x^v = 1}`, `v i₀ > 0`, is `cosetPt η B w` for the
fixed matrix `B = fiberMat v i₀`, one of finitely many torsion `η`, and a torsion `w`. -/
theorem exists_fiber_param {r' : ℕ} (v : Fin (r' + 1) → ℤ) (i₀ : Fin (r' + 1)) (hm : 0 < v i₀)
    (x : Fin (r' + 1) → ℂˣ) (hx : ∀ j, IsRootOfUnityC (x j : ℂ)) (hv : charPow x v = 1) :
    ∃ ζ ∈ (Polynomial.nthRoots (v i₀).toNat (1 : ℂ)).toFinset, ∃ w : Fin r' → ℂ,
      (∀ k, w k ≠ 0) ∧ (∀ k, IsRootOfUnityC (w k)) ∧
        cosetPt (fiberEta i₀ ζ) (fiberMat v i₀) w = fun j => (x j : ℂ) := by
  classical
  set m := (v i₀).toNat with hmdef
  have hm' : (m : ℤ) = v i₀ := Int.toNat_of_nonneg hm.le
  have hm0 : 0 < m := by omega
  have hw : ∀ k, ∃ w : ℂ, w ^ m = (x (i₀.succAbove k) : ℂ) := fun k =>
    IsAlgClosed.exists_pow_nat_eq _ hm0
  choose w hw using hw
  have hw0 : ∀ k, w k ≠ 0 := fun k h => by
    have := hw k
    rw [h, zero_pow hm0.ne'] at this
    exact (x _).ne_zero this.symm
  have hwtor : ∀ k, IsRootOfUnityC (w k) := fun k => by
    obtain ⟨n, hn, h⟩ := hx (i₀.succAbove k)
    exact ⟨m * n, Nat.mul_pos hm0 hn, by rw [pow_mul, hw k, h]⟩
  set ζ := (x i₀ : ℂ) * ∏ k, w k ^ v (i₀.succAbove k) with hζdef
  have hζ : ζ ^ m = 1 := by
    have h1 : (charPow x v : ℂ) = 1 := by rw [hv, Units.val_one]
    rw [coe_charPow, Fin.prod_univ_succAbove _ i₀] at h1
    have hk : ∀ k, (w k ^ v (i₀.succAbove k)) ^ m =
        (x (i₀.succAbove k) : ℂ) ^ v (i₀.succAbove k) := fun k => by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw k]
    rw [hζdef, mul_pow, ← Finset.prod_pow]
    simp_rw [hk]
    rw [← hm', zpow_natCast] at h1
    exact h1
  refine ⟨ζ, ?_, w, hw0, hwtor, ?_⟩
  · rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hm0]
    exact hζ
  funext j
  rcases Fin.eq_self_or_eq_succAbove i₀ j with rfl | ⟨k, rfl⟩
  · simp only [cosetPt, fiberEta, fiberMat, ite_true, zpow_neg, Finset.prod_inv_distrib]
    rw [hζdef, mul_assoc,
      mul_inv_cancel₀ (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw0 k)), mul_one]
  · simp only [cosetPt, fiberEta, fiberMat, Fin.succAbove_ne, ite_false,
      Fin.succAbove_right_inj, one_mul]
    rw [Finset.prod_eq_single k]
    · simp only [ite_true]
      rw [← hm', zpow_natCast, hw k]
    · intro b _ hb
      simp [Ne.symm hb]
    · simp

/-- **Finite cover of a character fiber.** For `v ≠ 0` there are finitely many torsion
points `η` and one exponent matrix `B` of size `(r'+1) × r'` with `B.mulVec` injective such
that every torsion point of `{x^v = 1}` is `cosetPt η B w` with `w` torsion. -/
theorem exists_fiber_cover {r' : ℕ} (v : Fin (r' + 1) → ℤ) (hv : v ≠ 0) :
    ∃ (F : Finset (Fin (r' + 1) → ℂ)) (B : Matrix (Fin (r' + 1)) (Fin r') ℤ),
      (∀ η ∈ F, ∀ j, IsRootOfUnityC (η j)) ∧ Function.Injective B.mulVec ∧
      ∀ x : Fin (r' + 1) → ℂˣ, (∀ j, IsRootOfUnityC (x j : ℂ)) → charPow x v = 1 →
        ∃ η ∈ F, ∃ w : Fin r' → ℂ, (∀ k, w k ≠ 0) ∧ (∀ k, IsRootOfUnityC (w k)) ∧
          cosetPt η B w = fun j => (x j : ℂ) := by
  classical
  obtain ⟨i₀, hi₀'⟩ := Function.ne_iff.1 hv
  have hi₀ : v i₀ ≠ 0 := hi₀'
  -- reduce to `v i₀ > 0`
  suffices key : ∀ v : Fin (r' + 1) → ℤ, 0 < v i₀ →
      ∃ (F : Finset (Fin (r' + 1) → ℂ)) (B : Matrix (Fin (r' + 1)) (Fin r') ℤ),
        (∀ η ∈ F, ∀ j, IsRootOfUnityC (η j)) ∧ Function.Injective B.mulVec ∧
        ∀ x : Fin (r' + 1) → ℂˣ, (∀ j, IsRootOfUnityC (x j : ℂ)) → charPow x v = 1 →
          ∃ η ∈ F, ∃ w : Fin r' → ℂ, (∀ k, w k ≠ 0) ∧ (∀ k, IsRootOfUnityC (w k)) ∧
            cosetPt η B w = fun j => (x j : ℂ) by
    rcases lt_or_gt_of_ne hi₀ with hneg | hpos
    · obtain ⟨F, B, hF, hB, h⟩ := key (-v) (by show (0 : ℤ) < -v i₀; omega)
      refine ⟨F, B, hF, hB, fun x hx hxv => h x hx ?_⟩
      rw [charPow_neg, hxv, inv_one]
    · exact key v hpos
  intro v hm
  refine ⟨(Polynomial.nthRoots (v i₀).toNat (1 : ℂ)).toFinset.image (fiberEta i₀), fiberMat v i₀,
    ?_, fiberMat_mulVec_injective v i₀ hm.ne', fun x hx hxv => ?_⟩
  · intro η hη j
    rw [Finset.mem_image] at hη
    obtain ⟨ζ, hζ, rfl⟩ := hη
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by omega)] at hζ
    simp only [fiberEta]
    split_ifs
    · exact ⟨(v i₀).toNat, by omega, hζ⟩
    · exact ⟨1, one_pos, one_pow 1⟩
  · obtain ⟨ζ, hζ, w, hw0, hwtor, hcos⟩ := exists_fiber_param v i₀ hm x hx hxv
    exact ⟨fiberEta i₀ ζ, Finset.mem_image_of_mem _ hζ, w, hw0, hwtor, hcos⟩

end IngramMello
