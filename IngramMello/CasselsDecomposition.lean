import IngramMello.CasselsHeight

/-!
# Conductor decomposition of cyclotomic integers

Decompose an element of `ℤ[ζ_(n*m)]` into powers
with exponents less than `n` and coefficients in `ℤ[ζ_m]`. For coprime conductors the
powers can be taken of `ζ_n`; otherwise they are powers of `ζ_(n*m)`.
The proof uses division by a monic polynomial, without an integral basis.
-/

namespace IngramMello

open Polynomial

/-- Reduce a polynomial in `ξ` modulo `X^n - ξ^n`, keeping its coefficients in `S`. -/
theorem exists_sum_pow_of_mem_adjoin (S : Subalgebra ℤ ℂ) {n : ℕ} (hn : 0 < n)
    {ξ β : ℂ} (hξ : ξ ^ n ∈ S) (hβ : β ∈ Algebra.adjoin S {ξ}) :
    ∃ a : Fin n → ℂ, (∀ j, a j ∈ S) ∧ β = ∑ j, a j * ξ ^ (j : ℕ) := by
  classical
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hβ
  obtain ⟨f, hf⟩ := hβ
  change aeval ξ f = β at hf
  let q : S[X] := X ^ n - C ⟨ξ ^ n, hξ⟩
  have hq : q.Monic := monic_X_pow_sub_C _ hn.ne'
  have hdeg : q.natDegree = n := natDegree_X_pow_sub_C
  have hq1 : q ≠ 1 := by
    intro h
    have := congrArg natDegree h
    rw [hdeg, natDegree_one] at this
    omega
  have hrdeg : (f %ₘ q).natDegree < n := by
    simpa [hdeg] using natDegree_modByMonic_lt f hq hq1
  have hroot : aeval ξ q = 0 := by simp [q]
  refine ⟨fun j => ((f %ₘ q).coeff j : ℂ), fun j => ((f %ₘ q).coeff j).2, ?_⟩
  rw [← hf, ← aeval_modByMonic_eq_self_of_root hroot, aeval_eq_sum_range' hrdeg]
  change (∑ j ∈ Finset.range n, ((f %ₘ q).coeff j : ℂ) * ξ ^ j) = _
  exact (Fin.sum_univ_eq_sum_range (fun j => ((f %ₘ q).coeff j : ℂ) * ξ ^ j) n).symm

/-- A root of unity in a subalgebra has all its integer powers there as well. -/
theorem IsRootOfUnityC.zpow_mem_subalgebra {S : Subalgebra ℤ ℂ} {ξ : ℂ}
    (hξ : IsRootOfUnityC ξ) (hmem : ξ ∈ S) (k : ℤ) : ξ ^ k ∈ S := by
  obtain ⟨n, hn, hpow⟩ := hξ
  have hne : ξ ≠ 0 := by
    intro h
    simp [h, hn.ne'] at hpow
  have hreduce : ξ ^ k = ξ ^ (k % (n : ℤ)).toNat := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k n]
    rw [zpow_add₀ hne, zpow_mul, zpow_natCast, hpow, one_zpow, mul_one,
      ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hn.ne'))]
  rw [hreduce]
  exact S.pow_mem hmem _

/-- The natural power relation for a product conductor. -/
theorem zetaC_mul_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    zetaC (n * m) ^ n = zetaC m := by
  have h := zetaC_dvd (Nat.mul_pos hn hm) (dvd_mul_left m n)
  simpa [Nat.mul_div_cancel_left _ hm, Nat.mul_div_cancel _ hm] using h.symm

/-- **Decomposition for a product conductor.** No primality assumption is needed. -/
theorem exists_cycInt_sum_pow {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {β : ℂ} (hβ : β ∈ cycInt (n * m)) :
    ∃ a : Fin n → ℂ, (∀ j, a j ∈ cycInt m) ∧
      β = ∑ j, a j * zetaC (n * m) ^ (j : ℕ) := by
  have hle : cycInt (n * m) ≤
      (Algebra.adjoin (cycInt m) {zetaC (n * m)}).restrictScalars ℤ := by
    rw [cycInt, Algebra.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    change zetaC (n * m) ∈ Algebra.adjoin (cycInt m) {zetaC (n * m)}
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  apply exists_sum_pow_of_mem_adjoin (cycInt m) hn _ (hle hβ)
  rw [zetaC_mul_pow hn hm]
  exact Algebra.subset_adjoin (Set.mem_singleton _)

/-- Bézout expresses the generator for coprime conductors using the two smaller roots. -/
theorem zetaC_mul_eq_of_coprime {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hcop : n.Coprime m) :
    zetaC (n * m) = zetaC m ^ Nat.gcdA n m * zetaC n ^ Nat.gcdB n m := by
  have hne := (zetaC_isPrimitiveRoot (Nat.mul_pos hn hm)).ne_zero (Nat.mul_pos hn hm).ne'
  have hexp : (n : ℤ) * Nat.gcdA n m + (m : ℤ) * Nat.gcdB n m = 1 := by
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one, Nat.cast_one]
  calc zetaC (n * m)
      = zetaC (n * m) ^ ((n : ℤ) * Nat.gcdA n m + (m : ℤ) * Nat.gcdB n m) := by
          rw [hexp, zpow_one]
    _ = (zetaC (n * m) ^ n) ^ Nat.gcdA n m *
        (zetaC (n * m) ^ m) ^ Nat.gcdB n m := by
          rw [zpow_add₀ hne, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    _ = _ := by rw [zetaC_mul_pow hn hm, Nat.mul_comm n m, zetaC_mul_pow hm hn]

/-- **Decomposition for coprime conductors.** Coprime conductor factors allow powers of the
smaller root `ζ_n`. -/
theorem exists_cycInt_sum_pow_of_coprime {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hcop : n.Coprime m) {β : ℂ} (hβ : β ∈ cycInt (n * m)) :
    ∃ a : Fin n → ℂ, (∀ j, a j ∈ cycInt m) ∧
      β = ∑ j, a j * zetaC n ^ (j : ℕ) := by
  let S := (Algebra.adjoin (cycInt m) {zetaC n}).restrictScalars ℤ
  have hbase : cycInt m ≤ S := by
    intro x hx
    change x ∈ Algebra.adjoin (cycInt m) {zetaC n}
    exact (Algebra.adjoin (cycInt m) {zetaC n}).algebraMap_mem ⟨x, hx⟩
  have hroot : zetaC n ∈ S := by
    change zetaC n ∈ Algebra.adjoin (cycInt m) {zetaC n}
    exact Algebra.subset_adjoin (Set.mem_singleton _)
  have hle : cycInt (n * m) ≤ S := by
    rw [cycInt, Algebra.adjoin_le_iff, Set.singleton_subset_iff]
    rw [zetaC_mul_eq_of_coprime hn hm hcop]
    exact S.mul_mem (hbase (zetaC_zpow_mem_cycInt hm _))
      (IsRootOfUnityC.zpow_mem_subalgebra
        ⟨n, hn, (zetaC_isPrimitiveRoot hn).pow_eq_one⟩ hroot _)
  apply exists_sum_pow_of_mem_adjoin (cycInt m) hn _ (hle hβ)
  rw [(zetaC_isPrimitiveRoot hn).pow_eq_one]
  exact (cycInt m).one_mem

/-- The geometric sum that permits subtracting a common coefficient. -/
theorem sum_zetaC_pow {n : ℕ} (hn : 1 < n) :
    ∑ j : Fin n, zetaC n ^ (j : ℕ) = 0 := by
  rw [Fin.sum_univ_eq_sum_range]
  exact (zetaC_isPrimitiveRoot (by omega)).geom_sum_eq_zero hn

/-- Subtracting a common coefficient leaves the expansion unchanged. -/
theorem sum_sub_mul_zetaC_pow {n : ℕ} (hn : 1 < n) (a : Fin n → ℂ) (c : ℂ) :
    ∑ j, (a j - c) * zetaC n ^ (j : ℕ) = ∑ j, a j * zetaC n ^ (j : ℕ) := by
  simp_rw [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_zetaC_pow hn,
    mul_zero, sub_zero]

/-- Normalize any chosen coefficient to zero, preserving integrality at the lower level. -/
theorem exists_cycInt_sum_pow_sub {n m : ℕ} (hn : 1 < n) (hm : 0 < m)
    (hcop : n.Coprime m) {β : ℂ} (hβ : β ∈ cycInt (n * m)) :
    ∃ a : Fin n → ℂ, (∀ j, a j ∈ cycInt m) ∧
      ∀ i : Fin n, (∀ j, a j - a i ∈ cycInt m) ∧
        β = ∑ j, (a j - a i) * zetaC n ^ (j : ℕ) := by
  obtain ⟨a, ha, hsum⟩ := exists_cycInt_sum_pow_of_coprime (by omega) hm hcop hβ
  exact ⟨a, ha, fun i => ⟨fun j => (cycInt m).sub_mem (ha j) (ha i),
    hsum.trans (sum_sub_mul_zetaC_pow hn a (a i)).symm⟩⟩

/-- The concrete field `ℚ(ζ_n)` is a cyclotomic extension, without requiring the
ambient field `ℂ` to be algebraic over `ℚ`. -/
theorem cycField_isCyclotomicExtension {n : ℕ} (hn : 0 < n) :
    IsCyclotomicExtension {n} ℚ (cycField n) := by
  have : NeZero n := ⟨hn.ne'⟩
  exact (IntermediateField.isCyclotomicExtension_singleton_iff_eq_adjoin
    n ℚ ℂ (cycField n) (zetaC_isPrimitiveRoot hn)).2 rfl

/-- The ring of integers in `ℚ(ζ_n)` is `ℤ[ζ_n]`, as subsets of `ℂ`. -/
theorem mem_cycInt_iff {n : ℕ} (hn : 0 < n) {β : ℂ} :
    β ∈ cycInt n ↔ β ∈ cycField n ∧ IsIntegral ℤ β := by
  constructor
  · intro hβ
    exact ⟨mem_cycField_of_mem_cycInt hβ, isIntegral_of_mem_cycInt hn hβ⟩
  · rintro ⟨hβ, hint⟩
    have : NeZero n := ⟨hn.ne'⟩
    have := cycField_isCyclotomicExtension hn
    let ξ : cycField n := IntermediateField.AdjoinSimple.gen ℚ (zetaC n)
    have hξ : IsPrimitiveRoot ξ n :=
      IsPrimitiveRoot.coe_submonoidClass_iff.mp (zetaC_isPrimitiveRoot hn)
    have hβint : IsIntegral ℤ (⟨β, hβ⟩ : cycField n) :=
      (isIntegral_algHom_iff ((cycField n).val.restrictScalars ℤ)
        Subtype.val_injective).1 hint
    obtain ⟨y, hy⟩ :=
      (IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hξ).isIntegral_iff.1 hβint
    have hy' : ((y : cycField n) : ℂ) = β := congrArg Subtype.val hy
    have hmem : β ∈ (Algebra.adjoin ℤ {ξ}).map ((cycField n).val.restrictScalars ℤ) :=
      ⟨y, y.2, hy'⟩
    simpa [ξ, cycInt] using hmem

end IngramMello
