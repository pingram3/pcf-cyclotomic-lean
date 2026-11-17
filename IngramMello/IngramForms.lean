import Mathlib

/-!
# Ingram's critical forms

The input to Proposition 3 of the paper cited from P. Ingram, *A finiteness result for
post-critically finite polynomials*, Int. Math. Res. Not. IMRN 2012, no. 3, 524–543
(Lemma 2.5 there). Lemma numbers below refer to the arXiv version, arXiv:1010.3393,
where the statements are Lemmas 7 and 8.

For `c : Fin (d-1) → R` let `Phi d c` be the antiderivative, vanishing at `0`, of
`∏ (X - C (c i))`; this is Ingram's normal form `f_c` (up to the factor `d`): its
critical points are the `c i`. The forms `G d j = Phi_X (X_j)` are rational
polynomials in the `c i` with `aeval c (G d j) = (Phi d c).eval (c j)`.

* `Phi_eq_zero_of_forall_eval_crit` (Ingram's Lemma 7): if `Phi d c` vanishes at every
  `c j` then `c = 0` (any field of characteristic zero).
* `exists_certificate` (Nullstellensatz): `X_i ^ e = ∑ j, F i j * G d j` with
  `F i j` over `ℚ`.
* `Phi_comp_smul` (homogeneity): `Phi_{λc}(λ z) = λ^d Phi_c(z)`.
* `exists_ingram_local`: the ultrametric lower bound
  `v N₀ * v (c i) ^ d ≤ v (Phi_c (c j))` for some `j`, over any valued field of
  characteristic zero (Ingram's Lemma 8, local part).
-/

namespace IngramMello

open Polynomial

section Defs

variable {R : Type*} [CommRing R]

/-- `∏ i, (X - C (c i))`. -/
noncomputable def critProd {n : ℕ} (c : Fin n → R) : R[X] := ∏ i, (X - C (c i))

theorem critProd_monic {n : ℕ} (c : Fin n → R) : (critProd c).Monic :=
  monic_prod_of_monic _ _ fun i _ => monic_X_sub_C (c i)

theorem critProd_natDegree [Nontrivial R] {n : ℕ} (c : Fin n → R) :
    (critProd c).natDegree = n := by
  unfold critProd
  rw [natDegree_prod_of_monic _ _ fun i _ => monic_X_sub_C (c i)]
  simp

theorem map_critProd {S : Type*} [CommRing S] (φ : R →+* S) {n : ℕ} (c : Fin n → R) :
    (critProd c).map φ = critProd (φ ∘ c) := by
  unfold critProd
  simp [Polynomial.map_prod]

variable [Algebra ℚ R]

/-- Ingram's normal form `Φ_c`: the antiderivative of `critProd c` vanishing at `0`.
Only `d ≥ 1` is meaningful (`critProd c` has degree `d - 1 < d`). -/
noncomputable def Phi (d : ℕ) (c : Fin (d - 1) → R) : R[X] :=
  ∑ k ∈ Finset.range d, C (((k : ℚ) + 1)⁻¹ • (critProd c).coeff k) * X ^ (k + 1)

theorem derivative_Phi (d : ℕ) (hd : 1 ≤ d) (c : Fin (d - 1) → R) :
    derivative (Phi d c) = critProd c := by
  unfold Phi
  rw [derivative_sum]
  conv_rhs => rw [(critProd c).as_sum_range' d (by
    rcases subsingleton_or_nontrivial R with h | h
    · simp [Subsingleton.elim (critProd c) 0]; omega
    · rw [critProd_natDegree]; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [derivative_C_mul_X_pow, Nat.add_sub_cancel, ← C_mul_X_pow_eq_monomial]
  congr 2
  have h1 : (algebraMap ℚ R) ((k : ℚ) + 1)⁻¹ * ((k : R) + 1) = 1 := by
    rw [show ((k : R) + 1) = algebraMap ℚ R ((k : ℚ) + 1) by simp, ← map_mul,
      inv_mul_cancel₀ (by positivity), map_one]
  rw [Algebra.smul_def, Nat.cast_add_one, mul_assoc, mul_comm ((critProd c).coeff k),
    ← mul_assoc, h1, one_mul]

theorem eval_zero_Phi (d : ℕ) (c : Fin (d - 1) → R) : (Phi d c).eval 0 = 0 := by
  unfold Phi
  simp [eval_finsetSum]

theorem map_Phi {S : Type*} [CommRing S] [Algebra ℚ S] (φ : R →ₐ[ℚ] S) (d : ℕ)
    (c : Fin (d - 1) → R) : (Phi d c).map φ = Phi d (φ ∘ c) := by
  unfold Phi
  rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : (critProd (φ ∘ c)).coeff k = φ ((critProd c).coeff k) := by
    have := congrArg (fun P => P.coeff k) (map_critProd (φ : R →+* S) c)
    simpa [coeff_map] using this.symm
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, AlgHom.coe_toRingHom, h,
    map_smul]

end Defs

section Forms

variable (d : ℕ)

/-- Ingram's forms `G_j(c) = Φ_c(c_j)`, as rational polynomials in `c`. -/
noncomputable def G (j : Fin (d - 1)) : MvPolynomial (Fin (d - 1)) ℚ :=
  (Phi d fun i => MvPolynomial.X i).eval (MvPolynomial.X j)

theorem algHom_eval {R S : Type*} [CommRing R] [CommRing S] [Algebra ℚ R] [Algebra ℚ S]
    (φ : R →ₐ[ℚ] S) (P : R[X]) (x : R) : φ (P.eval x) = (P.map φ).eval (φ x) := by
  rw [eval_map]
  exact (eval₂_hom (φ : R →+* S) x).symm

theorem aeval_G {R : Type*} [CommRing R] [Algebra ℚ R] (c : Fin (d - 1) → R) (j : Fin (d - 1)) :
    MvPolynomial.aeval c (G d j) = (Phi d c).eval (c j) := by
  unfold G
  rw [algHom_eval, map_Phi]
  simp [Function.comp_def]

end Forms

section NoCommonRoot

variable {k : Type*} [Field k] [CharZero k]

/-- **Ingram, Lemma 7.** If `Φ_c` vanishes at every critical point `c j`, then `c = 0`. -/
theorem Phi_eq_zero_of_forall_eval_crit (d : ℕ) (hd : 2 ≤ d) (c : Fin (d - 1) → k)
    (h : ∀ j, (Phi d c).eval (c j) = 0) : c = 0 := by
  classical
  set P := Phi d c with hP
  have hP' : derivative P = critProd c := derivative_Phi d (by omega) c
  have hP0 : P ≠ 0 := by
    intro h0
    have := hP'
    rw [h0, derivative_zero] at this
    exact (critProd_monic c).ne_zero this.symm
  have hdeg : P.natDegree ≤ d := by
    rw [hP]; unfold Phi
    refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by
      have := Finset.mem_range.mp hi; omega)
  have hroots : (critProd c).roots = Finset.univ.val.map c := by
    unfold critProd
    rw [Finset.prod_eq_multiset_prod, show (Multiset.map (fun i => X - C (c i)) Finset.univ.val)
      = Multiset.map (fun a => X - C a) (Multiset.map c Finset.univ.val) by
      rw [Multiset.map_map]; rfl, roots_multiset_prod_X_sub_C]
  have hmult : ∀ j, (Finset.univ.val.map c).count (c j) + 1 ≤ P.roots.count (c j) := by
    intro j
    have h1 : (Finset.univ.val.map c).count (c j) = P.rootMultiplicity (c j) - 1 := by
      rw [← hroots, count_roots, ← hP', derivative_rootMultiplicity_of_root (h j)]
    have h2 : 0 < P.rootMultiplicity (c j) := (rootMultiplicity_pos hP0).mpr (h j)
    rw [count_roots, h1]; omega
  set T : Finset k := insert 0 (Finset.univ.val.map c).toFinset with hT
  have hTle : ∀ α ∈ T, (Finset.univ.val.map c).count α + 1 ≤ P.roots.count α := by
    intro α hα
    rw [hT, Finset.mem_insert, Multiset.mem_toFinset, Multiset.mem_map] at hα
    rcases hα with rfl | ⟨j, -, rfl⟩
    · by_cases h0 : ∃ j, c j = 0
      · obtain ⟨j, hj⟩ := h0
        rw [← hj]; exact hmult j
      · push Not at h0
        have hc0 : (Finset.univ.val.map c).count 0 = 0 := by
          rw [Multiset.count_eq_zero, Multiset.mem_map]
          rintro ⟨j, -, hj⟩
          exact h0 j hj
        rw [hc0, count_roots]
        exact (rootMultiplicity_pos hP0).mpr (eval_zero_Phi d c)
    · exact hmult j
  have hsub : T ⊆ P.roots.toFinset := by
    intro α hα
    rw [Multiset.mem_toFinset, ← Multiset.count_pos]
    have := hTle α hα; omega
  have hsum1 : ∑ α ∈ T, ((Finset.univ.val.map c).count α + 1) ≤ ∑ α ∈ T, P.roots.count α :=
    Finset.sum_le_sum hTle
  have hsum2 : ∑ α ∈ T, P.roots.count α ≤ d := by
    calc ∑ α ∈ T, P.roots.count α ≤ ∑ α ∈ P.roots.toFinset, P.roots.count α :=
          Finset.sum_le_sum_of_subset hsub
      _ = Multiset.card P.roots := Multiset.toFinset_sum_count_eq _
      _ ≤ P.natDegree := card_roots' P
      _ ≤ d := hdeg
  have hsum3 : ∑ α ∈ T, (Finset.univ.val.map c).count α = d - 1 := by
    rw [← Finset.sum_subset (Finset.subset_insert _ _) (fun x _ hx => by
      rwa [Multiset.count_eq_zero, ← Multiset.mem_toFinset]),
      Multiset.toFinset_sum_count_eq]
    simp
  rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, hsum3] at hsum1
  have hcard : T.card ≤ 1 := by omega
  have hT0 : ∀ α ∈ T, α = 0 := by
    intro α hα
    exact Finset.card_le_one.mp hcard α hα 0 (Finset.mem_insert_self _ _)
  funext j
  exact hT0 (c j) (Finset.mem_insert_of_mem (Multiset.mem_toFinset.mpr
    (Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val _, rfl⟩)))

end NoCommonRoot

section Certificate

/-- **Nullstellensatz certificate** (Ingram, proof of Lemma 8): `X_i ^ e` lies in the
ideal generated by the forms `G d j`, with rational polynomial coefficients. -/
theorem exists_certificate (d : ℕ) (hd : 2 ≤ d) :
    ∃ (e : ℕ) (F : Fin (d - 1) → Fin (d - 1) → MvPolynomial (Fin (d - 1)) ℚ), 0 < e ∧
      ∀ i, MvPolynomial.X i ^ e = ∑ j, F i j * G d j := by
  classical
  set I : Ideal (MvPolynomial (Fin (d - 1)) ℚ) := Ideal.span (Set.range (G d)) with hI
  have hrad : ∀ i, MvPolynomial.X i ∈ I.radical := by
    intro i
    rw [← MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := ℂ),
      MvPolynomial.mem_vanishingIdeal_iff]
    intro x hx
    have hx0 : x = 0 := by
      apply Phi_eq_zero_of_forall_eval_crit d hd x
      intro j
      rw [← aeval_G]
      exact hx _ (Ideal.subset_span ⟨j, rfl⟩)
    simp [hx0]
  choose e he using fun i => (Ideal.mem_radical_iff.mp (hrad i))
  have hmem : ∀ i, MvPolynomial.X i ^ (Finset.univ.sup e + 1) ∈ I := by
    intro i
    have : Finset.univ.sup e + 1 = e i + (Finset.univ.sup e + 1 - e i) := by
      have := Finset.le_sup (f := e) (Finset.mem_univ i); omega
    rw [this, pow_add]
    exact I.mul_mem_right _ (he i)
  have hspan : ∀ i, ∃ F : Fin (d - 1) → MvPolynomial (Fin (d - 1)) ℚ,
      ∑ j, F j * G d j = MvPolynomial.X i ^ (Finset.univ.sup e + 1) := by
    intro i
    have := (Submodule.mem_span_range_iff_exists_fun (MvPolynomial (Fin (d - 1)) ℚ)).mp (hmem i)
    simpa [smul_eq_mul] using this
  choose F hF using hspan
  exact ⟨_, F, Nat.succ_pos _, fun i => (hF i).symm⟩

end Certificate

section Homog

variable {F : Type*} [Field F] [CharZero F]

/-- Homogeneity: `Φ_{λc}(λ z) = λ^d Φ_c(z)`, as polynomials in `z`. -/
theorem Phi_comp_smul (d : ℕ) (hd : 1 ≤ d) (c : Fin (d - 1) → F) (l : F) :
    (Phi d fun i => l * c i).comp (C l * X) = C (l ^ d) * Phi d c := by
  have hl : C l * C l ^ (d - 1) = C (l ^ d) := by
    rw [← C_pow, ← C_mul, ← pow_succ', Nat.sub_add_cancel hd]
  have hder : derivative ((Phi d fun i => l * c i).comp (C l * X) - C (l ^ d) * Phi d c) = 0 := by
    simp only [derivative_sub, derivative_comp, derivative_Phi d hd, derivative_mul, derivative_C,
      derivative_X, zero_mul, zero_add, mul_one]
    unfold critProd
    rw [prod_comp]
    simp only [sub_comp, X_comp, C_comp]
    have : ∀ i, C l * X - C (l * c i) = C l * (X - C (c i)) := fun i => by rw [C_mul, mul_sub]
    simp_rw [this]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      ← mul_assoc, hl, sub_self]
  have h0 : ((Phi d fun i => l * c i).comp (C l * X) - C (l ^ d) * Phi d c).eval 0 = 0 := by
    simp [eval_comp, eval_zero_Phi]
  have := eq_C_of_derivative_eq_zero hder
  rw [coeff_zero_eq_eval_zero, h0, C_0] at this
  exact sub_eq_zero.mp this

theorem Phi_eval_smul (d : ℕ) (hd : 1 ≤ d) (c : Fin (d - 1) → F) (l z : F) :
    (Phi d fun i => l * c i).eval (l * z) = l ^ d * (Phi d c).eval z := by
  have := congrArg (eval z) (Phi_comp_smul d hd c l)
  simpa [eval_comp] using this

end Homog

section Denominators

/-- A positive integer clearing the denominators of all coefficients of `F`. -/
def denClear {σ : Type*} (F : MvPolynomial σ ℚ) : ℕ := ∏ m ∈ F.support, (F.coeff m).den

theorem denClear_pos {σ : Type*} (F : MvPolynomial σ ℚ) : 0 < denClear F :=
  Finset.prod_pos fun _ _ => Rat.den_pos _

theorem den_dvd_denClear {σ : Type*} (F : MvPolynomial σ ℚ) (m : σ →₀ ℕ) :
    (F.coeff m).den ∣ denClear F := by
  by_cases hm : m ∈ F.support
  · exact Finset.dvd_prod_of_mem _ hm
  · rw [MvPolynomial.notMem_support_iff.mp hm]; simp

theorem exists_int_mul_coeff {σ : Type*} (F : MvPolynomial σ ℚ) (N : ℕ)
    (hN : ∀ m', (F.coeff m').den ∣ N) (m : σ →₀ ℕ) : ∃ z : ℤ, (N : ℚ) * F.coeff m = z := by
  obtain ⟨t, ht⟩ := hN m
  refine ⟨(F.coeff m).num * t, ?_⟩
  rw [ht]; push_cast
  have h := Rat.mul_den_eq_num (F.coeff m)
  linear_combination (t : ℚ) * h

end Denominators

section ValInt

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

theorem val_natCast_le_one (n : ℕ) : v (n : F) ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_succ]; exact v.map_add_le ih (by simp)

theorem val_intCast_le_one (z : ℤ) : v (z : F) ≤ 1 := by
  rcases Int.eq_nat_or_neg z with ⟨n, rfl | rfl⟩
  · exact_mod_cast val_natCast_le_one v n
  · rw [Int.cast_neg, Valuation.map_neg]; exact_mod_cast val_natCast_le_one v n

/-- A rational polynomial with denominators dividing `N`, evaluated at a point of the
valuation ring, has `v (N * value) ≤ 1`. -/
theorem val_natCast_mul_aeval_le_one [CharZero F] {σ : Type*} (P : MvPolynomial σ ℚ) (N : ℕ)
    (hN : ∀ m, (P.coeff m).den ∣ N) (x : σ → F) (hx : ∀ i, v (x i) ≤ 1) :
    v ((N : F) * MvPolynomial.aeval x P) ≤ 1 := by
  rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq,
    Finset.mul_sum]
  refine v.map_sum_le fun m _ => ?_
  obtain ⟨z, hz⟩ := exists_int_mul_coeff P N hN m
  have : (N : F) * (algebraMap ℚ F (P.coeff m) * ∏ i ∈ m.support, x i ^ m i)
      = (z : F) * ∏ i ∈ m.support, x i ^ m i := by
    rw [← mul_assoc]; congr 1
    rw [eq_ratCast, ← Rat.cast_natCast, ← Rat.cast_mul, hz, Rat.cast_intCast]
  rw [this, Valuation.map_mul]
  calc v (z : F) * v (∏ i ∈ m.support, x i ^ m i) ≤ 1 * 1 := by
        refine mul_le_mul' (val_intCast_le_one v z) ?_
        rw [map_prod]
        exact Finset.prod_le_one fun i _ => by rw [Valuation.map_pow]; exact pow_le_one' (hx i) _
    _ = 1 := mul_one 1

end ValInt

section Local

universe u w

/-- **Ingram, Lemma 8 (local part), ultrametric form.** There is `N₀ = N₀(d) ≥ 1` such that
for every valued field `F` of characteristic zero and every `c`, some critical value
satisfies `v N₀ * v (c i) ^ d ≤ v (Φ_c (c j))`. The constant is `1` whenever `v` is trivial
on `ℤ ∖ {0}`. -/
theorem exists_ingram_local (d : ℕ) (hd : 2 ≤ d) :
    ∃ N₀ : ℕ, 0 < N₀ ∧
      ∀ (F : Type u) [Field F] [CharZero F] (Γ₀ : Type w) [LinearOrderedCommGroupWithZero Γ₀]
        (v : Valuation F Γ₀) (c : Fin (d - 1) → F) (i : Fin (d - 1)),
        ∃ j, v (N₀ : F) * v (c i) ^ d ≤ v ((Phi d c).eval (c j)) := by
  classical
  obtain ⟨e, Fc, he, hFc⟩ := exists_certificate d hd
  refine ⟨∏ i, ∏ j, denClear (Fc i j),
    Finset.prod_pos fun i _ => Finset.prod_pos fun j _ => denClear_pos _, ?_⟩
  intro F _ _ Γ₀ _ v c i
  set N₀ : ℕ := ∏ i, ∏ j, denClear (Fc i j) with hN₀
  have hden : ∀ i j m, ((Fc i j).coeff m).den ∣ N₀ := fun i j m =>
    (den_dvd_denClear _ m).trans ((Finset.dvd_prod_of_mem _ (Finset.mem_univ j)).trans
      (Finset.dvd_prod_of_mem (fun i => ∏ j, denClear (Fc i j)) (Finset.mem_univ i)))
  have hN0ne : v (N₀ : F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact Nat.cast_ne_zero.mpr (Finset.prod_pos fun i _ =>
      Finset.prod_pos fun j _ => denClear_pos _).ne'
  by_cases hci : c i = 0
  · exact ⟨i, by rw [hci, Valuation.map_zero, zero_pow (by omega), mul_zero]; exact zero_le⟩
  have hne : (Finset.univ : Finset (Fin (d - 1))).Nonempty := ⟨i, Finset.mem_univ i⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun k => v (c k)) hne
  have hvi₀ : v (c i₀) ≠ 0 := by
    intro h0
    have := hi₀ i (Finset.mem_univ i)
    rw [h0] at this
    exact hci ((Valuation.zero_iff v).mp (le_antisymm this zero_le))
  have hci₀ : c i₀ ≠ 0 := fun h => hvi₀ (by rw [h, Valuation.map_zero])
  set x : Fin (d - 1) → F := fun k => c k * (c i₀)⁻¹ with hx
  have hcx : ∀ k, c k = c i₀ * x k := fun k => by
    rw [hx]; simp only; field_simp
  have hx1 : ∀ k, v (x k) ≤ 1 := fun k => by
    rw [hx]; simp only
    rw [Valuation.map_mul, map_inv₀]
    calc v (c k) * (v (c i₀))⁻¹ ≤ v (c i₀) * (v (c i₀))⁻¹ :=
          mul_le_mul_left (hi₀ k (Finset.mem_univ k)) _
      _ = 1 := mul_inv_cancel₀ hvi₀
  have hxi₀ : x i₀ = 1 := by rw [hx]; simp only; exact mul_inv_cancel₀ hci₀
  have hcert : (1 : F) = ∑ j, MvPolynomial.aeval x (Fc i₀ j) * (Phi d x).eval (x j) := by
    have := congrArg (MvPolynomial.aeval x) (hFc i₀)
    rw [map_pow, MvPolynomial.aeval_X, hxi₀, one_pow, map_sum] at this
    simpa [aeval_G] using this
  have hhom : ∀ j, (Phi d c).eval (c j) = c i₀ ^ d * (Phi d x).eval (x j) := by
    intro j
    have hc : c = fun k => c i₀ * x k := funext hcx
    calc (Phi d c).eval (c j) = (Phi d fun k => c i₀ * x k).eval (c i₀ * x j) := by
          rw [← hcx j, ← hc]
      _ = c i₀ ^ d * (Phi d x).eval (x j) := Phi_eval_smul d (by omega) x (c i₀) (x j)
  by_contra hcon
  push Not at hcon
  have hlt : ∀ j, v ((Phi d x).eval (x j)) < v (N₀ : F) := by
    intro j
    have h1 := hcon j
    rw [hhom j, Valuation.map_mul, Valuation.map_pow] at h1
    have h2 : v (N₀ : F) * v (c i) ^ d ≤ v (N₀ : F) * v (c i₀) ^ d :=
      mul_le_mul_right (pow_le_pow_left' (hi₀ i (Finset.mem_univ i)) d) _
    have h3 := lt_of_lt_of_le h1 h2
    rw [mul_comm (v (N₀ : F))] at h3
    exact lt_of_mul_lt_mul_left' h3
  have hsum : v ((N₀ : F) * ∑ j, MvPolynomial.aeval x (Fc i₀ j) * (Phi d x).eval (x j))
      < v (N₀ : F) := by
    rw [Finset.mul_sum]
    refine v.map_sum_lt hN0ne fun j _ => ?_
    rw [← mul_assoc, Valuation.map_mul]
    calc v ((N₀ : F) * MvPolynomial.aeval x (Fc i₀ j)) * v ((Phi d x).eval (x j))
        ≤ 1 * v ((Phi d x).eval (x j)) :=
          mul_le_mul_left (val_natCast_mul_aeval_le_one v _ N₀ (hden i₀ j) x hx1) _
      _ = v ((Phi d x).eval (x j)) := one_mul _
      _ < v (N₀ : F) := hlt j
  rw [← hcert, mul_one] at hsum
  exact lt_irrefl _ hsum

end Local

end IngramMello
