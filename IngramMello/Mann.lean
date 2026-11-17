import IngramMello.Statements

/-!
# Mann's theorem on vanishing sums of roots of unity

Source: H. B. Mann, *On linear relations between roots of unity*, Mathematika 12 (1965),
107–117. Rational-coefficient form: in a minimal vanishing relation `∑ cᵢ ζᵢ = 0` among `k`
roots of unity with rational coefficients, all ratios `ζᵢ/ζⱼ` satisfy
`(ζᵢ/ζⱼ)^{k!} = 1` (`IngramMello.mann`). The proof uses only the irreducibility of
cyclotomic polynomials over `ℚ` (through embeddings `ℚ⟮ω⟯ → ℂ`) and the geometric
sum of a primitive `p`-th root of unity. This is the arithmetic input for the proof
of `Laurent`.
-/

namespace IngramMello

open Polynomial Finset IntermediateField

/-! ### The Fourier identity for a primitive `p`-th root of unity -/

/-- `∑_{m<p} ξ^{m a} = p` if `p ∣ a` and `0` otherwise, for a primitive `p`-th root `ξ`,
`p` prime. -/
theorem sum_pow_mul_primitiveRoot {p : ℕ} (hp : p.Prime) {ξ : ℂ} (hξ : IsPrimitiveRoot ξ p)
    (a : ℕ) :
    ∑ m ∈ range p, ξ ^ (m * a) = if p ∣ a then (p : ℂ) else 0 := by
  have h1 : ∀ m, ξ ^ (m * a) = (ξ ^ a) ^ m := fun m => by rw [mul_comm, pow_mul]
  simp_rw [h1]
  split_ifs with hd
  · rw [(hξ.pow_eq_one_iff_dvd a).2 hd]
    simp
  · have hcop : a.Coprime p := (Nat.coprime_comm).1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hd)
    exact (hξ.pow_of_coprime a hcop).geom_sum_eq_zero hp.one_lt

/-! ### Embeddings of `ℚ⟮ω⟯` moving `ω` to `ω^b` -/

/-- For `b` coprime to `n`, there is a `ℚ`-embedding of `ℚ⟮ω⟯` into `ℂ` sending the
primitive `n`-th root `ω` to `ω ^ b`. -/
theorem exists_algHom_pow_of_coprime {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n)
    {b : ℕ} (hb : b.Coprime n) :
    ∃ σ : ℚ⟮ω⟯ →ₐ[ℚ] ℂ, σ (IntermediateField.AdjoinSimple.gen ℚ ω) = ω ^ b := by
  have hint : IsIntegral ℚ ω := (hω.isIntegral hn).tower_top
  have hroot : aeval (ω ^ b) (minpoly ℚ (IntermediateField.adjoin.powerBasis hint).gen) = 0 := by
    rw [IntermediateField.adjoin.powerBasis_gen, IntermediateField.minpoly_gen,
      ← cyclotomic_eq_minpoly_rat hω hn, aeval_def, ← eval_map, map_cyclotomic]
    have : NeZero (n : ℂ) := ⟨by exact_mod_cast hn.ne'⟩
    exact (isRoot_cyclotomic_iff.2 (hω.pow_of_coprime b hb))
  refine ⟨(IntermediateField.adjoin.powerBasis hint).lift (ω ^ b) hroot, ?_⟩
  have := (IntermediateField.adjoin.powerBasis hint).lift_gen (ω ^ b) hroot
  rwa [IntermediateField.adjoin.powerBasis_gen] at this

/-- Applying an embedding `σ` with `σ ω = ω^b` to a rational relation among powers of `ω`. -/
theorem sum_pow_mul_eq_zero_of_algHom {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n)
    {b : ℕ} (hb : b.Coprime n) {k : ℕ} (c : Fin k → ℚ) (a : Fin k → ℕ)
    (hsum : ∑ i, (c i : ℂ) * ω ^ a i = 0) :
    ∑ i, (c i : ℂ) * ω ^ (b * a i) = 0 := by
  obtain ⟨σ, hσ⟩ := exists_algHom_pow_of_coprime hn hω hb
  set g := IntermediateField.AdjoinSimple.gen ℚ ω
  have hg : (g : ℂ) = ω := rfl
  have hin : ∑ i, (algebraMap ℚ ℚ⟮ω⟯ (c i)) * g ^ a i = 0 := by
    apply Subtype.ext
    simpa [hg] using hsum
  have := congrArg σ hin
  rw [map_sum, map_zero] at this
  simpa [hσ, pow_mul] using this

/-! ### The one-prime step -/

/-- For `m < p`, the residue class filter `p ∣ a + (p - j)` means `a ≡ j (mod p)`; two
different classes `j ≠ j'` are disjoint. -/
theorem eq_of_dvd_add_sub {p a j j' : ℕ} (hj : j < p) (hj' : j' < p)
    (h : p ∣ a + (p - j)) (h' : p ∣ a + (p - j')) : j = j' := by
  rcases le_total j j' with hle | hle
  · have hd : p ∣ (a + (p - j)) - (a + (p - j')) := Nat.dvd_sub h h'
    have he : (a + (p - j)) - (a + (p - j')) = j' - j := by omega
    rw [he] at hd
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have hd : p ∣ (a + (p - j')) - (a + (p - j)) := Nat.dvd_sub h' h
    have he : (a + (p - j')) - (a + (p - j)) = j - j' := by omega
    rw [he] at hd
    have := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega

/-- **One-prime step of Mann's theorem.** Let `ω` be a primitive `n`-th root of unity,
`p` a prime dividing `n`, and `∑ cᵢ ω^{aᵢ} = 0` a minimal rational relation with
`p ∣ a i₀` for some `i₀`. Then either every `aᵢ` is divisible by `p`, or `p ≤ k` and
`p² ∤ n`. -/
theorem mann_prime_step {n : ℕ} (hn : 0 < n) {ω : ℂ} (hω : IsPrimitiveRoot ω n)
    {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) {k : ℕ} (c : Fin k → ℚ) (a : Fin k → ℕ)
    (i₀ : Fin k) (h₀ : p ∣ a i₀)
    (hsum : ∑ i, (c i : ℂ) * ω ^ a i = 0)
    (hmin : ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (c i : ℂ) * ω ^ a i = 0 → I = univ) :
    (∀ i, p ∣ a i) ∨ (p ≤ k ∧ ¬ p ∣ n / p) := by
  classical
  set q := n / p with hq
  have hnq : n = q * p := (Nat.div_mul_cancel hpn).symm
  set ξ := ω ^ q with hξdef
  have hξ : IsPrimitiveRoot ξ p := hω.pow hn hnq
  have hξ0 : ξ ≠ 0 := hξ.ne_zero hp.ne_zero
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  -- the conjugate relations
  set R : ℕ → ℂ := fun m => ∑ i, (c i : ℂ) * ω ^ a i * ξ ^ (m * a i) with hR
  have hRzero : ∀ m, Nat.Coprime (1 + m * q) n → R m = 0 := by
    intro m hm
    have := sum_pow_mul_eq_zero_of_algHom hn hω hm c a hsum
    simp only [hR]
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_assoc, hξdef, ← pow_mul, ← pow_add]
    congr 2
    ring
  -- residue classes
  set A : ℕ → ℂ := fun j => ∑ i ∈ univ.filter (fun i => p ∣ a i + (p - j)), (c i : ℂ) * ω ^ a i
    with hA
  -- Fourier inversion
  have hfourier : ∀ j, ∑ m ∈ range p, ξ ^ (m * (p - j)) * R m = (p : ℂ) * A j := by
    intro j
    simp only [hR, hA, Finset.mul_sum]
    rw [Finset.sum_comm]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : ∀ m, ξ ^ (m * (p - j)) * ((c i : ℂ) * ω ^ a i * ξ ^ (m * a i)) =
        (c i : ℂ) * ω ^ a i * ξ ^ (m * (a i + (p - j))) := by
      intro m
      rw [mul_add, pow_add]
      ring
    simp_rw [this, ← Finset.mul_sum, sum_pow_mul_primitiveRoot hp hξ]
    split_ifs <;> ring
  -- the bad set
  set Bad := (range p).filter (fun m => ¬ Nat.Coprime (1 + m * q) n) with hBad
  have hbad_dvd : ∀ m ∈ Bad, p ∣ 1 + m * q := by
    intro m hm
    rw [hBad, Finset.mem_filter] at hm
    obtain ⟨r, hr, hr1, hrn⟩ := Nat.Prime.not_coprime_iff_dvd.1 hm.2
    by_cases hrp : r = p
    · exact hrp ▸ hr1
    · exfalso
      have hrq : r ∣ q := by
        rw [hnq] at hrn
        rcases (Nat.Prime.dvd_mul hr).1 hrn with h | h
        · exact h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr hp).1 h) hrp
      have : r ∣ 1 := (Nat.dvd_add_left (dvd_mul_of_dvd_right hrq m)).1 hr1
      exact hr.one_lt.ne' (Nat.dvd_one.1 this)
  have hbad_notq : ∀ m ∈ Bad, ¬ p ∣ q := by
    intro m hm hpq
    have : p ∣ 1 := (Nat.dvd_add_left (dvd_mul_of_dvd_right hpq m)).1 (hbad_dvd m hm)
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hbad_card : Bad.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro m hm m' hm'
    have hmp : m < p := Finset.mem_range.1 (Finset.mem_filter.1 hm).1
    have hm'p : m' < p := Finset.mem_range.1 (Finset.mem_filter.1 hm').1
    have hd := hbad_dvd m hm
    have hd' := hbad_dvd m' hm'
    have hnq' := hbad_notq m hm
    rcases le_total m m' with hle | hle
    · have h1 : p ∣ (1 + m' * q) - (1 + m * q) := Nat.dvd_sub hd' hd
      have h2 : (1 + m' * q) - (1 + m * q) = (m' - m) * q := by
        rw [Nat.sub_mul]; omega
      rw [h2] at h1
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
      · have := Nat.eq_zero_of_dvd_of_lt h (by omega); omega
      · exact absurd h hnq'
    · have h1 : p ∣ (1 + m * q) - (1 + m' * q) := Nat.dvd_sub hd hd'
      have h2 : (1 + m * q) - (1 + m' * q) = (m - m') * q := by
        rw [Nat.sub_mul]; omega
      rw [h2] at h1
      rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
      · have := Nat.eq_zero_of_dvd_of_lt h (by omega); omega
      · exact absurd h hnq'
  -- only the bad terms survive
  have hkey : ∀ j, (p : ℂ) * A j = ∑ m ∈ Bad, ξ ^ (m * (p - j)) * R m := by
    intro j
    rw [← hfourier j, hBad]
    symm
    apply Finset.sum_filter_of_ne
    intro m _ hne hcop
    exact hne (by rw [hRzero m hcop, mul_zero])
  -- `A 0 = 0 ↔ A j = 0`
  have hiff : ∀ j, (A 0 = 0 ↔ A j = 0) := by
    intro j
    have hcases : Bad = ∅ ∨ ∃ m₀, Bad = {m₀} := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hbad_card with h | h
      · exact Or.inl (Finset.card_eq_zero.1 h)
      · exact Or.inr (Finset.card_eq_one.1 h)
    rcases hcases with hB | ⟨m₀, hB⟩
    · have h0 : A 0 = 0 := by
        have := hkey 0; rw [hB, Finset.sum_empty] at this
        exact (mul_eq_zero.1 this).resolve_left hp0
      have hj : A j = 0 := by
        have := hkey j; rw [hB, Finset.sum_empty] at this
        exact (mul_eq_zero.1 this).resolve_left hp0
      exact ⟨fun _ => hj, fun _ => h0⟩
    · have h0 := hkey 0
      have hj := hkey j
      rw [hB, Finset.sum_singleton] at h0 hj
      have e0 : A 0 = 0 ↔ R m₀ = 0 := by
        constructor
        · intro h
          rw [h, mul_zero] at h0
          rcases mul_eq_zero.1 h0.symm with h' | h'
          · exact absurd h' (pow_ne_zero _ hξ0)
          · exact h'
        · intro h
          rw [h, mul_zero] at h0
          exact (mul_eq_zero.1 h0).resolve_left hp0
      have ej : A j = 0 ↔ R m₀ = 0 := by
        constructor
        · intro h
          rw [h, mul_zero] at hj
          rcases mul_eq_zero.1 hj.symm with h' | h'
          · exact absurd h' (pow_ne_zero _ hξ0)
          · exact h'
        · intro h
          rw [h, mul_zero] at hj
          exact (mul_eq_zero.1 hj).resolve_left hp0
      rw [e0, ej]
  have hA0_of_dvd : p ∣ q → A 0 = 0 := by
    intro hpq
    have hB : Bad = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro m hm
      exact hbad_notq m hm hpq
    have := hkey 0
    rw [hB, Finset.sum_empty] at this
    exact (mul_eq_zero.1 this).resolve_left hp0
  -- conclusion
  by_cases hA0 : A 0 = 0
  · left
    have hmem : i₀ ∈ univ.filter (fun i => p ∣ a i + (p - 0)) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.sub_zero]
      exact dvd_add h₀ dvd_rfl
    have huniv := hmin _ ⟨i₀, hmem⟩ hA0
    intro i
    have hi : i ∈ univ.filter (fun i => p ∣ a i + (p - 0)) := by
      rw [huniv]; exact Finset.mem_univ i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Nat.sub_zero] at hi
    exact (Nat.dvd_add_left dvd_rfl).1 hi
  · right
    refine ⟨?_, fun hpq => hA0 (hA0_of_dvd hpq)⟩
    have hne : ∀ j : Fin p, (univ.filter (fun i => p ∣ a i + (p - (j : ℕ)))).Nonempty := by
      intro j
      apply Finset.nonempty_of_sum_ne_zero (f := fun i => (c i : ℂ) * ω ^ a i)
      exact fun h => hA0 ((hiff j).2 h)
    choose f hf using hne
    have hinj : Function.Injective f := by
      intro j j' hjj'
      have h1 := Finset.mem_filter.1 (hf j)
      have h2 := Finset.mem_filter.1 (hf j')
      rw [hjj'] at h1
      exact Fin.ext (eq_of_dvd_add_sub j.isLt j'.isLt h1.2 h2.2)
    simpa using Fintype.card_le_of_injective f hinj

/-! ### Mann's theorem -/

/-- A finite family of roots of unity has a common positive exponent. -/
theorem exists_common_exponent {k : ℕ} (ζ : Fin k → ℂ) (hζ : ∀ i, IsRootOfUnityC (ζ i)) :
    ∃ n : ℕ, 0 < n ∧ ∀ i, ζ i ^ n = 1 := by
  choose N hN using hζ
  refine ⟨∏ i, N i, Finset.prod_pos fun i _ => (hN i).1, fun i => ?_⟩
  obtain ⟨t, ht⟩ := Finset.dvd_prod_of_mem N (Finset.mem_univ i)
  rw [ht, pow_mul, (hN i).2, one_pow]

/-- **Mann's theorem, normalized form.** In a minimal vanishing relation `∑ cᵢ ζᵢ = 0`
among `k` roots of unity with rational coefficients, one of which is `1`, every
`ζᵢ` satisfies `ζᵢ^{k!} = 1`. -/
theorem mann_normalized {k : ℕ} (c : Fin k → ℚ) (ζ : Fin k → ℂ)
    (hζ : ∀ i, IsRootOfUnityC (ζ i)) (i₀ : Fin k) (h₀ : ζ i₀ = 1)
    (hsum : ∑ i, (c i : ℂ) * ζ i = 0)
    (hmin : ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (c i : ℂ) * ζ i = 0 → I = univ) :
    ∀ i, ζ i ^ k.factorial = 1 := by
  classical
  have hex := exists_common_exponent ζ hζ
  set n := Nat.find hex with hndef
  have hn : 0 < n ∧ ∀ i, ζ i ^ n = 1 := Nat.find_spec hex
  have hnmin : ∀ m, m < n → ¬ (0 < m ∧ ∀ i, ζ i ^ m = 1) := fun m hm => Nat.find_min hex hm
  have hn0 : n ≠ 0 := hn.1.ne'
  have : NeZero n := ⟨hn0⟩
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / n) with hωdef
  have hω : IsPrimitiveRoot ω n := Complex.isPrimitiveRoot_exp n hn0
  have hpow : ∀ i, ∃ j, j < n ∧ ω ^ j = ζ i := fun i => by
    obtain ⟨j, hj, hjω⟩ := hω.eq_pow_of_pow_eq_one (hn.2 i)
    exact ⟨j, hj, hjω⟩
  choose a ha using hpow
  have hζa : ζ = fun i => ω ^ a i := funext fun i => ((ha i).2).symm
  have hsum' : ∑ i, (c i : ℂ) * ω ^ a i = 0 := by rw [hζa] at hsum; exact hsum
  have hmin' : ∀ I : Finset (Fin k), I.Nonempty →
      ∑ i ∈ I, (c i : ℂ) * ω ^ a i = 0 → I = univ := by
    rw [hζa] at hmin; exact hmin
  have h₀' : ω ^ a i₀ = 1 := by rw [(ha i₀).2]; exact h₀
  -- every prime factor of `n` is `≤ k` and simple
  have hsq : ∀ p : ℕ, p.Prime → p ∣ n → p ≤ k ∧ ¬ p ∣ n / p := by
    intro p hp hpn
    have h₀'' : p ∣ a i₀ := by
      have : n ∣ a i₀ := (hω.pow_eq_one_iff_dvd _).1 h₀'
      exact dvd_trans hpn this
    rcases mann_prime_step hn.1 hω hp hpn c a i₀ h₀'' hsum' hmin' with h | h
    · exfalso
      apply hnmin (n / p) (Nat.div_lt_self hn.1 hp.one_lt)
      refine ⟨Nat.div_pos (Nat.le_of_dvd hn.1 hpn) hp.pos, fun i => ?_⟩
      rw [← (ha i).2, ← pow_mul, hω.pow_eq_one_iff_dvd]
      obtain ⟨t, ht⟩ := h i
      refine ⟨t, ?_⟩
      rw [ht, mul_assoc, ← mul_assoc p, mul_comm p t, mul_assoc, Nat.mul_div_cancel' hpn,
        mul_comm]
    · exact h
  have hsf : Squarefree n := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    have hpn : p ∣ n := dvd_trans (dvd_mul_right p p) hpp
    exact (hsq p hp hpn).2 (Nat.dvd_div_of_mul_dvd hpp)
  have hdvd : n ∣ k.factorial := by
    rw [← Nat.prod_primeFactors_of_squarefree hsf]
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Nat.prime_of_mem_primeFactors hp).prime
    · intro p hp
      have hp' := Nat.prime_of_mem_primeFactors hp
      exact (Nat.Prime.dvd_factorial hp').2 (hsq p hp' (Nat.dvd_of_mem_primeFactors hp)).1
  intro i
  obtain ⟨t, ht⟩ := hdvd
  rw [ht, pow_mul, hn.2 i, one_pow]

theorem IsRootOfUnityC.ne_zero {ζ : ℂ} (h : IsRootOfUnityC ζ) : ζ ≠ 0 := by
  obtain ⟨n, hn, hζ⟩ := h
  rintro rfl
  rw [zero_pow hn.ne'] at hζ
  exact zero_ne_one hζ

theorem IsRootOfUnityC.mul {ζ₁ ζ₂ : ℂ} (h₁ : IsRootOfUnityC ζ₁) (h₂ : IsRootOfUnityC ζ₂) :
    IsRootOfUnityC (ζ₁ * ζ₂) := by
  obtain ⟨n₁, hn₁, h₁⟩ := h₁
  obtain ⟨n₂, hn₂, h₂⟩ := h₂
  refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, ?_⟩
  rw [mul_pow, pow_mul, h₁, one_pow, mul_comm n₁, pow_mul, h₂, one_pow, one_mul]

theorem IsRootOfUnityC.inv {ζ : ℂ} (h : IsRootOfUnityC ζ) : IsRootOfUnityC ζ⁻¹ := by
  obtain ⟨n, hn, hζ⟩ := h
  exact ⟨n, hn, by rw [inv_pow, hζ, inv_one]⟩

theorem IsRootOfUnityC.pow {ζ : ℂ} (h : IsRootOfUnityC ζ) (m : ℕ) : IsRootOfUnityC (ζ ^ m) := by
  obtain ⟨n, hn, hζ⟩ := h
  exact ⟨n, hn, by rw [← pow_mul, mul_comm, pow_mul, hζ, one_pow]⟩

theorem IsRootOfUnityC.zpow {ζ : ℂ} (h : IsRootOfUnityC ζ) (m : ℤ) : IsRootOfUnityC (ζ ^ m) := by
  rcases Int.natAbs_eq m with hm | hm
  · rw [hm, zpow_natCast]; exact h.pow _
  · rw [hm, zpow_neg, zpow_natCast]; exact (h.pow _).inv

/-- **Mann's theorem** (rational coefficients). In a minimal vanishing relation
`∑ cᵢ ζᵢ = 0` among `k` roots of unity with `cᵢ ∈ ℚ`, all `ζᵢ^{k!}` coincide. -/
theorem mann {k : ℕ} (c : Fin k → ℚ) (ζ : Fin k → ℂ) (hζ : ∀ i, IsRootOfUnityC (ζ i))
    (hsum : ∑ i, (c i : ℂ) * ζ i = 0)
    (hmin : ∀ I : Finset (Fin k), I.Nonempty → ∑ i ∈ I, (c i : ℂ) * ζ i = 0 → I = univ)
    (i j : Fin k) : ζ i ^ k.factorial = ζ j ^ k.factorial := by
  have hj0 : ζ j ≠ 0 := (hζ j).ne_zero
  have hj0' : (ζ j)⁻¹ ≠ 0 := inv_ne_zero hj0
  have h := mann_normalized c (fun i => ζ i * (ζ j)⁻¹) (fun i => (hζ i).mul (hζ j).inv) j
    (mul_inv_cancel₀ hj0)
    (by simp_rw [← mul_assoc, ← Finset.sum_mul, hsum, zero_mul])
    (by
      intro I hI h
      apply hmin I hI
      simp_rw [← mul_assoc, ← Finset.sum_mul] at h
      exact (mul_eq_zero.1 h).resolve_right hj0') i
  simp only [mul_pow, inv_pow] at h
  exact (mul_inv_eq_one₀ (pow_ne_zero _ hj0)).1 h

end IngramMello
