import IngramMello.CasselsIdentities

/-!
# Loxton's theorem, qualitative form

A qualitative form of Loxton's theorem (J. H. Loxton, *On the maximum modulus of cyclotomic
integers*, Acta Arith. 22 (1972), 69–85): every cyclotomic integer `β` with Cassels height
`M_P(β) ≤ B` is a sum of at most `Λ(B)` roots of unity, for a constant `Λ(B)` independent of
the conductor `P` (`loxton_qualitative`). Hence algebraic integers of bounded house in
cyclotomic fields are sums of a bounded number of roots of unity (`loxton_house`). No explicit
value of `Λ(B)` is extracted.

The first step (`loxton_sumRoots_bound`, Loxton's Lemma 9 extended to all conductors) shows
that `β ∈ R_P` is a sum of at most `2^{ω(P)} M_P(β)` roots of unity. The rest is an induction
on `B` in steps of `1/2`, using Cassels' identities and Cassels' majority lemma.
-/

namespace IngramMello

open Finset

/-- Number of distinct prime factors of a product with a prime, dividing case. -/
theorem card_primeFactors_mul_of_dvd {p P₁ : ℕ} (hp : p.Prime) (hP₁ : 0 < P₁) (hdvd : p ∣ P₁) :
    (p * P₁).primeFactors.card = P₁.primeFactors.card := by
  rw [Nat.primeFactors_mul hp.ne_zero hP₁.ne', hp.primeFactors]
  congr 1
  rw [Finset.union_eq_right]
  intro q hq
  rw [Finset.mem_singleton] at hq
  rw [hq, Nat.mem_primeFactors]
  exact ⟨hp, hdvd, hP₁.ne'⟩

/-- Number of distinct prime factors of a product with a prime, coprime case. -/
theorem card_primeFactors_mul_of_not_dvd {p P₁ : ℕ} (hp : p.Prime) (hP₁ : 0 < P₁)
    (hndvd : ¬ p ∣ P₁) :
    (p * P₁).primeFactors.card = P₁.primeFactors.card + 1 := by
  rw [Nat.primeFactors_mul hp.ne_zero hP₁.ne', hp.primeFactors, Finset.singleton_union,
    Finset.card_insert_of_notMem]
  rw [Nat.mem_primeFactors]
  exact fun h => hndvd h.2.1

/-- **Loxton's Lemma 9, extended to all conductors.** Every `β ∈ R_P` is a sum of at most
`2^{ω(P)} · M_P(β)` roots of unity, where `ω(P)` is the number of prime factors of `P`. -/
theorem loxton_sumRoots_bound : ∀ P : ℕ, 0 < P → ∀ β ∈ cycInt P,
    ∃ k : ℕ, (k : ℝ) ≤ 2 ^ P.primeFactors.card * cassM P β ∧ β ∈ SumRoots k := by
  intro P
  induction P using Nat.strong_induction_on with
  | _ P ih =>
  intro hP β hβ
  rcases eq_or_ne P 1 with rfl | hP1
  · obtain ⟨k, hk, hmem⟩ := exists_mem_sumRoots_of_mem_cycInt_one hβ
    exact ⟨k, by simpa using hk, hmem⟩
  -- a prime factor
  obtain ⟨p, hp, P₁, hPeq⟩ : ∃ p : ℕ, p.Prime ∧ ∃ P₁, P = p * P₁ :=
    ⟨P.minFac, Nat.minFac_prime hP1, Nat.minFac_dvd P⟩
  have hP₁ : 0 < P₁ := Nat.pos_of_mul_pos_left (hPeq ▸ hP)
  have hP₁lt : P₁ < P := by
    rw [hPeq]
    have := hp.two_le
    nlinarith
  have hcassM_nonneg := cassM_nonneg P β
  -- the inductive hypothesis as a choice function
  have ih' : ∀ γ ∈ cycInt P₁, ∃ k : ℕ,
      (k : ℝ) ≤ 2 ^ P₁.primeFactors.card * cassM P₁ γ ∧ γ ∈ SumRoots k :=
    ih P₁ hP₁lt hP₁
  subst hPeq
  by_cases hdvd : p ∣ P₁
  · -- case (b): `p ∣ P₁`
    obtain ⟨a, ha, hsum⟩ := exists_cycInt_sum_pow hp.pos hP₁ hβ
    choose k hk hkmem using fun j => ih' (a j) (ha j)
    refine ⟨∑ j, k j, ?_, ?_⟩
    · rw [card_primeFactors_mul_of_dvd hp hP₁ hdvd, hsum,
        cassels_identity_dvd hp hP₁ hdvd a (fun j => mem_cycField_of_mem_cycInt (ha j)),
        Finset.mul_sum]
      push_cast
      exact Finset.sum_le_sum fun j _ => hk j
    · rw [hsum]
      refine SumRoots.sum _ _ _ fun j _ => ?_
      rw [mul_comm]
      exact SumRoots.mul_root ⟨p * P₁, Nat.mul_pos hp.pos hP₁, by
        rw [← pow_mul, mul_comm (j : ℕ), pow_mul, (zetaC_isPrimitiveRoot
          (Nat.mul_pos hp.pos hP₁)).pow_eq_one, one_pow]⟩ (hkmem j)
  · -- case (a): `p ∤ P₁`
    have hcop : p.Coprime P₁ := (Nat.Prime.coprime_iff_not_dvd hp).2 hdvd
    obtain ⟨a, ha, hdec⟩ := exists_cycInt_sum_pow_sub hp.one_lt hP₁ hcop hβ
    choose k hk hkmem using fun i j => ih' (a j - a i) ((hdec i).1 j)
    have hne : Nonempty (Fin p) := ⟨⟨0, hp.pos⟩⟩
    obtain ⟨i₀, hi₀⟩ := Finite.exists_min fun i : Fin p => ∑ j, k i j
    refine ⟨∑ j, k i₀ j, ?_, ?_⟩
    · -- the counting inequality
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have h1 : (p : ℝ) * ∑ j, (k i₀ j : ℝ) ≤ ∑ i, ∑ j, (k i j : ℝ) := by
        have : ∀ i : Fin p, ∑ j, (k i₀ j : ℝ) ≤ ∑ j, (k i j : ℝ) := fun i => by
          exact_mod_cast hi₀ i
        calc (p : ℝ) * ∑ j, (k i₀ j : ℝ) = ∑ _i : Fin p, ∑ j, (k i₀ j : ℝ) := by
              rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          _ ≤ ∑ i, ∑ j, (k i j : ℝ) := Finset.sum_le_sum fun i _ => this i
      have h2 : ∑ i, ∑ j, (k i j : ℝ) ≤
          2 ^ P₁.primeFactors.card * ∑ i, ∑ j, cassM P₁ (a i - a j) := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [← cassM_neg, neg_sub]
        exact hk i j
      have h3 : ∑ i, ∑ j, cassM P₁ (a i - a j) =
          2 * ((p : ℝ) - 1) * cassM (p * P₁) β := by
        rw [(hdec i₀).2]
        rw [← cassels_identity_coprime hp hP₁ hdvd a (fun j => mem_cycField_of_mem_cycInt (ha j))]
        rw [sum_sub_mul_zetaC_pow hp.one_lt]
      have h4 : 2 * ((p : ℝ) - 1) * cassM (p * P₁) β ≤ 2 * p * cassM (p * P₁) β := by
        nlinarith
      rw [card_primeFactors_mul_of_not_dvd hp hP₁ hdvd, pow_succ]
      push_cast
      have h5 : (p : ℝ) * ∑ j, (k i₀ j : ℝ) ≤
          (p : ℝ) * (2 ^ P₁.primeFactors.card * 2 * cassM (p * P₁) β) := by
        calc (p : ℝ) * ∑ j, (k i₀ j : ℝ) ≤ ∑ i, ∑ j, (k i j : ℝ) := h1
          _ ≤ 2 ^ P₁.primeFactors.card * ∑ i, ∑ j, cassM P₁ (a i - a j) := h2
          _ = 2 ^ P₁.primeFactors.card * (2 * ((p : ℝ) - 1) * cassM (p * P₁) β) := by rw [h3]
          _ ≤ 2 ^ P₁.primeFactors.card * (2 * p * cassM (p * P₁) β) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = (p : ℝ) * (2 ^ P₁.primeFactors.card * 2 * cassM (p * P₁) β) := by ring
      exact le_of_mul_le_mul_left h5 hp0
    · rw [(hdec i₀).2]
      refine SumRoots.sum _ _ _ fun j _ => ?_
      rw [mul_comm]
      exact SumRoots.mul_root ⟨p, hp.pos, by
        rw [← pow_mul, mul_comm (j : ℕ), pow_mul, (zetaC_isPrimitiveRoot hp.pos).pow_eq_one,
          one_pow]⟩ (hkmem i₀ j)

/-! ### Supporting lemmas -/

/-- A cyclotomic integer of Cassels height `< 1` is zero. -/
theorem eq_zero_of_cassM_lt_one {P : ℕ} (hP : 0 < P) {β : ℂ} (hβ : β ∈ cycInt P)
    (h : cassM P β < 1) : β = 0 := by
  by_contra hne
  exact absurd (one_le_cassM hP (mem_cycField_of_mem_cycInt hβ) (isIntegral_of_mem_cycInt hP hβ)
    hne) (not_le.2 h)

/-- The number of nonzero coefficients is bounded by the sum of their heights. -/
theorem card_filter_ne_zero_le_sum_cassM {P₁ : ℕ} (hP₁ : 0 < P₁) {n : ℕ} (c : Fin n → ℂ)
    (hc : ∀ j, c j ∈ cycInt P₁) :
    (((univ : Finset (Fin n)).filter fun j => c j ≠ 0).card : ℝ) ≤ ∑ j, cassM P₁ (c j) := by
  rw [Finset.card_eq_sum_ones, Nat.cast_sum]
  push_cast
  calc (∑ j ∈ (univ : Finset (Fin n)).filter (fun j => c j ≠ 0), (1 : ℝ))
      ≤ ∑ j ∈ (univ : Finset (Fin n)).filter (fun j => c j ≠ 0), cassM P₁ (c j) := by
        refine Finset.sum_le_sum fun j hj => ?_
        rw [Finset.mem_filter] at hj
        exact one_le_cassM hP₁ (mem_cycField_of_mem_cycInt (hc j))
          (isIntegral_of_mem_cycInt hP₁ (hc j)) hj.2
    _ ≤ ∑ j, cassM P₁ (c j) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun j _ _ => cassM_nonneg _ _

/-- The pointwise bound behind the counting argument in the coprime case. -/
theorem cassM_sub_ge_ite (P : ℕ) (x y : ℂ) :
    (if y = 0 then cassM P x else 0) + (if x = 0 then cassM P y else 0) ≤ cassM P (x - y) := by
  by_cases hy : y = 0 <;> by_cases hx : x = 0 <;> simp [hx, hy, cassM_zero, cassM_nonneg, cassM_neg]

/-- Summation of the pointwise bound: `2 Z T ≤ ∑_{i,j} M(c_i - c_j)`. -/
theorem two_mul_card_mul_sum_le {P : ℕ} {n : ℕ} (c : Fin n → ℂ) :
    2 * ((((univ : Finset (Fin n)).filter fun j => c j = 0).card : ℝ) * ∑ i, cassM P (c i)) ≤
      ∑ i, ∑ j, cassM P (c i - c j) := by
  have hsplit : ∀ f : Fin n → ℝ, ∑ i, ∑ j, (if c j = 0 then f i else 0) =
      (((univ : Finset (Fin n)).filter fun j => c j = 0).card : ℝ) * ∑ i, f i := by
    intro f
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  calc 2 * ((((univ : Finset (Fin n)).filter fun j => c j = 0).card : ℝ) * ∑ i, cassM P (c i))
      = ∑ i, ∑ j, (if c j = 0 then cassM P (c i) else 0) +
          ∑ i, ∑ j, (if c i = 0 then cassM P (c j) else 0) := by
        rw [Finset.sum_comm (f := fun i j => if c i = 0 then cassM P (c j) else 0), hsplit]
        ring
    _ = ∑ i, ∑ j, ((if c j = 0 then cassM P (c i) else 0) +
          (if c i = 0 then cassM P (c j) else 0)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Finset.sum_add_distrib]
    _ ≤ ∑ i, ∑ j, cassM P (c i - c j) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => cassM_sub_ge_ite P _ _

/-- The real inequalities of the coprime case. -/
theorem loxton_ineq {p Z X : ℕ} {T B M : ℝ} (hB : 1 ≤ B) (hM : M ≤ B) (_hT0 : 0 ≤ T)
    (hZX : Z + X = p) (hZ : (p : ℝ) < 2 * Z) (hA : (Z : ℝ) * T ≤ ((p : ℝ) - 1) * M)
    (hXT : (X : ℝ) ≤ T) (hp : 4 * B ^ 2 + 2 * B < p) :
    T ≤ B + 1 / 2 ∧ (X = 1 → T ≤ B) := by
  have hZX' : (Z : ℝ) + X = p := by exact_mod_cast hZX
  have hX0 : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hZ0 : (0 : ℝ) ≤ Z := Nat.cast_nonneg Z
  have hp1 : (1 : ℝ) < p := by nlinarith
  constructor
  · -- `X < 2B`
    have hX2B : (X : ℝ) < 2 * B := by
      by_contra hcon
      push Not at hcon
      have h1 : (Z : ℝ) * X ≤ Z * T := mul_le_mul_of_nonneg_left hXT hZ0
      have h2 : (Z : ℝ) * (2 * B) ≤ Z * X := mul_le_mul_of_nonneg_left hcon hZ0
      nlinarith
    -- `Z > 4B²`
    have hZbig : 4 * B ^ 2 < (Z : ℝ) := by nlinarith
    by_contra hcon
    push Not at hcon
    have h3 : (Z : ℝ) * (B + 1 / 2) < Z * T :=
      mul_lt_mul_of_pos_left hcon (by nlinarith)
    nlinarith
  · intro hX1
    subst hX1
    have hZp : (Z : ℝ) = p - 1 := by push_cast at hZX'; linarith
    rw [hZp] at hA
    have := le_of_mul_le_mul_left hA (by linarith : (0 : ℝ) < p - 1)
    linarith

/-- **Cassels' majority lemma, qualitative form.** If `M_{pP₁}(∑ a_j ζ_p^j) ≤ B` and
`p > 4B`, then more than half of the `a_j` coincide. -/
theorem cassels_majority {p P₁ : ℕ} (hp : p.Prime) (hP₁ : 0 < P₁) (hndvd : ¬ p ∣ P₁)
    (a : Fin p → ℂ) (ha : ∀ j, a j ∈ cycInt P₁) {B : ℝ}
    (hM : cassM (p * P₁) (∑ j, a j * zetaC p ^ (j : ℕ)) ≤ B) (hpB : 4 * B < p) :
    ∃ i₀ : Fin p,
      (p : ℝ) < 2 * (((univ : Finset (Fin p)).filter fun j => a j - a i₀ = 0).card) := by
  have hB0 : 0 ≤ B := (cassM_nonneg _ _).trans hM
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  -- the count of differing coefficients
  have hN : ∀ i : Fin p, ((((univ : Finset (Fin p)).filter fun j => a j - a i ≠ 0).card : ℝ)) ≤
      ∑ j, cassM P₁ (a i - a j) := by
    intro i
    have := card_filter_ne_zero_le_sum_cassM hP₁ (fun j => a j - a i)
      (fun j => (cycInt P₁).sub_mem (ha j) (ha i))
    refine this.trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
    rw [← cassM_neg, neg_sub]
  have hsum : ∑ i, ((((univ : Finset (Fin p)).filter fun j => a j - a i ≠ 0).card : ℝ)) ≤
      2 * ((p : ℝ) - 1) * B := by
    calc ∑ i, ((((univ : Finset (Fin p)).filter fun j => a j - a i ≠ 0).card : ℝ))
        ≤ ∑ i, ∑ j, cassM P₁ (a i - a j) := Finset.sum_le_sum fun i _ => hN i
      _ = 2 * ((p : ℝ) - 1) * cassM (p * P₁) (∑ j, a j * zetaC p ^ (j : ℕ)) :=
          (cassels_identity_coprime hp hP₁ hndvd a
            (fun j => mem_cycField_of_mem_cycInt (ha j))).symm
      _ ≤ 2 * ((p : ℝ) - 1) * B := by
          have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
          exact mul_le_mul_of_nonneg_left hM (by linarith)
  by_contra hcon
  push Not at hcon
  -- every `i` has at least `p/2` differing coefficients
  have hlow : ∀ i : Fin p, (p : ℝ) ≤
      2 * ((((univ : Finset (Fin p)).filter fun j => a j - a i ≠ 0).card : ℝ)) := by
    intro i
    have h := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin p)))
      (fun j => a j - a i = 0)
    rw [Finset.card_univ, Fintype.card_fin] at h
    have h' : ((((univ : Finset (Fin p)).filter fun j => a j - a i = 0).card : ℝ)) +
        ((((univ : Finset (Fin p)).filter fun j => ¬ a j - a i = 0).card : ℝ)) = p := by
      exact_mod_cast h
    have := hcon i
    simp only [ne_eq]
    linarith
  have htot : (p : ℝ) * p ≤
      2 * ∑ i, ((((univ : Finset (Fin p)).filter fun j => a j - a i ≠ 0).card : ℝ)) := by
    rw [Finset.mul_sum]
    calc (p : ℝ) * p = ∑ _i : Fin p, (p : ℝ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum fun i _ => hlow i
  nlinarith

/-- **Assembly lemma** for the inductive step, in the cases `q ∣ P₁` and `q ∤ P₁`. -/
theorem sum_mem_sumRoots_of_bounds {P₁ : ℕ} (hP₁ : 0 < P₁) {B : ℝ} (hB : 1 ≤ B) {Λ Λ' : ℕ}
    (hΛ : ⌈2 * B⌉₊ * Λ' ≤ Λ)
    (hinner : ∀ γ ∈ cycInt P₁, cassM P₁ γ ≤ B → γ ∈ SumRoots Λ)
    (houter : ∀ γ ∈ cycInt P₁, cassM P₁ γ ≤ B - 1 / 2 → γ ∈ SumRoots Λ')
    {n : ℕ} (c : Fin n → ℂ) (hc : ∀ j, c j ∈ cycInt P₁) (ρ : Fin n → ℂ)
    (hρ : ∀ j, IsRootOfUnityC (ρ j)) (hT : ∑ j, cassM P₁ (c j) ≤ B + 1 / 2)
    (hT1 : ((univ : Finset (Fin n)).filter fun j => c j ≠ 0).card = 1 →
      ∑ j, cassM P₁ (c j) ≤ B) :
    ∑ j, c j * ρ j ∈ SumRoots Λ := by
  set S := (univ : Finset (Fin n)).filter fun j => c j ≠ 0 with hS
  have hsumS : ∑ j, c j * ρ j = ∑ j ∈ S, c j * ρ j := by
    rw [hS, Finset.sum_filter_of_ne]
    intro j _ hj h0
    exact hj (by rw [h0, zero_mul])
  have hcard : (S.card : ℝ) ≤ ∑ j, cassM P₁ (c j) := card_filter_ne_zero_le_sum_cassM hP₁ c hc
  have hone : ∀ j ∈ S, 1 ≤ cassM P₁ (c j) := fun j hj => by
    rw [hS, Finset.mem_filter] at hj
    exact one_le_cassM hP₁ (mem_cycField_of_mem_cycInt (hc j))
      (isIntegral_of_mem_cycInt hP₁ (hc j)) hj.2
  have hSle : ∑ j ∈ S, cassM P₁ (c j) ≤ ∑ j, cassM P₁ (c j) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun j _ _ => cassM_nonneg _ _
  have hSceil : S.card ≤ ⌈2 * B⌉₊ := by
    have h1 : (S.card : ℝ) < 2 * B := by linarith
    have h2 : (2 * B : ℝ) ≤ ⌈2 * B⌉₊ := Nat.le_ceil _
    exact_mod_cast h1.le.trans h2
  rw [hsumS]
  rcases Nat.lt_or_ge S.card 2 with hlt | hge
  · have h01 : S.card = 0 ∨ S.card = 1 := by omega
    rcases h01 with h | h
    · rw [Finset.card_eq_zero.1 h, Finset.sum_empty]
      exact SumRoots.zero_mem Λ
    · obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.1 h
      rw [hj₀, Finset.sum_singleton, mul_comm]
      have hM : cassM P₁ (c j₀) ≤ B :=
        (Finset.single_le_sum (fun j _ => cassM_nonneg P₁ (c j)) (Finset.mem_univ j₀)).trans
          (hT1 h)
      exact SumRoots.mul_root (hρ j₀) (hinner _ (hc j₀) hM)
  · have hsmall : ∀ j ∈ S, cassM P₁ (c j) ≤ B - 1 / 2 := by
      intro j hj
      have h1 : ∑ i ∈ S, cassM P₁ (c i) = cassM P₁ (c j) + ∑ i ∈ S.erase j, cassM P₁ (c i) :=
        (Finset.add_sum_erase S _ hj).symm
      have h2 : ((S.erase j).card : ℝ) ≤ ∑ i ∈ S.erase j, cassM P₁ (c i) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        push_cast
        exact Finset.sum_le_sum fun i hi => hone i (Finset.mem_of_mem_erase hi)
      have h3 : (S.erase j).card = S.card - 1 := Finset.card_erase_of_mem hj
      have h4 : ((S.card - 1 : ℕ) : ℝ) = S.card - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      have h5 : (2 : ℝ) ≤ S.card := by exact_mod_cast hge
      rw [h3, h4] at h2
      linarith
    have hmem : ∑ j ∈ S, c j * ρ j ∈ SumRoots (∑ _j ∈ S, Λ') := by
      refine SumRoots.sum S _ _ fun j hj => ?_
      rw [mul_comm]
      exact SumRoots.mul_root (hρ j) (houter _ (hc j) (hsmall j hj))
    refine SumRoots.mono ?_ hmem
    rw [Finset.sum_const, smul_eq_mul]
    exact (Nat.mul_le_mul_right Λ' hSceil).trans hΛ

/-! ### The qualitative Loxton theorem -/

/-- The inner induction, for a fixed `B ≥ 1` given the constant `Λ'` for `B - 1/2`. -/
theorem loxton_step {B : ℝ} (hB : 1 ≤ B) {Λ' : ℕ}
    (hΛ' : ∀ P, 0 < P → ∀ β ∈ cycInt P, cassM P β ≤ B - 1 / 2 → β ∈ SumRoots Λ') :
    ∃ Λ : ℕ, ∀ P, 0 < P → ∀ β ∈ cycInt P, cassM P β ≤ B → β ∈ SumRoots Λ := by
  set p₀ : ℕ := ⌈4 * B ^ 2 + 2 * B⌉₊ + 1 with hp₀
  refine ⟨max ⌈(2 : ℝ) ^ p₀ * B⌉₊ (⌈2 * B⌉₊ * Λ'), ?_⟩
  set Λ := max ⌈(2 : ℝ) ^ p₀ * B⌉₊ (⌈2 * B⌉₊ * Λ') with hΛ
  intro P
  induction P using Nat.strong_induction_on with
  | _ P ih =>
  intro hP β hβ hM
  by_cases hsmall : ∀ q ∈ P.primeFactors, q < p₀
  · -- case (i): all prime factors are small; `loxton_sumRoots_bound`
    have hω : P.primeFactors.card ≤ p₀ := by
      calc P.primeFactors.card ≤ (Finset.range p₀).card :=
            Finset.card_le_card fun q hq => Finset.mem_range.2 (hsmall q hq)
        _ = p₀ := Finset.card_range p₀
    obtain ⟨k, hk, hmem⟩ := loxton_sumRoots_bound P hP β hβ
    refine SumRoots.mono ?_ hmem
    have h1 : (k : ℝ) ≤ 2 ^ p₀ * B := by
      calc (k : ℝ) ≤ 2 ^ P.primeFactors.card * cassM P β := hk
        _ ≤ 2 ^ p₀ * B :=
          mul_le_mul (pow_le_pow_right₀ (by norm_num) hω) hM (cassM_nonneg _ _) (by positivity)
    have h2 : k ≤ ⌈(2 : ℝ) ^ p₀ * B⌉₊ := by exact_mod_cast h1.trans (Nat.le_ceil _)
    exact h2.trans (le_max_left _ _)
  · push Not at hsmall
    obtain ⟨q, hqmem, hq₀⟩ := hsmall
    rw [Nat.mem_primeFactors] at hqmem
    obtain ⟨hq, hqdvd, -⟩ := hqmem
    obtain ⟨P₁, rfl⟩ := hqdvd
    have hP₁ : 0 < P₁ := Nat.pos_of_mul_pos_left hP
    have hP₁lt : P₁ < q * P₁ := by
      have := hq.two_le
      nlinarith
    have hinner : ∀ γ ∈ cycInt P₁, cassM P₁ γ ≤ B → γ ∈ SumRoots Λ := ih P₁ hP₁lt hP₁
    have houter : ∀ γ ∈ cycInt P₁, cassM P₁ γ ≤ B - 1 / 2 → γ ∈ SumRoots Λ' := hΛ' P₁ hP₁
    have hΛge : ⌈2 * B⌉₊ * Λ' ≤ Λ := le_max_right _ _
    have hq₀' : 4 * B ^ 2 + 2 * B < q := by
      have h1 : (4 * B ^ 2 + 2 * B : ℝ) ≤ ⌈4 * B ^ 2 + 2 * B⌉₊ := Nat.le_ceil _
      have h2 : (p₀ : ℝ) ≤ q := by exact_mod_cast hq₀
      rw [hp₀] at h2
      push_cast at h2
      linarith
    by_cases hdvd : q ∣ P₁
    · -- case (ii): `q ∣ P₁`
      obtain ⟨a, ha, hsum⟩ := exists_cycInt_sum_pow hq.pos hP₁ hβ
      have hT : ∑ j, cassM P₁ (a j) ≤ B := by
        rw [← cassels_identity_dvd hq hP₁ hdvd a (fun j => mem_cycField_of_mem_cycInt (ha j)),
          ← hsum]
        exact hM
      rw [hsum]
      exact sum_mem_sumRoots_of_bounds hP₁ hB hΛge hinner houter a ha
        (fun j => zetaC (q * P₁) ^ (j : ℕ))
        (fun j => ⟨q * P₁, Nat.mul_pos hq.pos hP₁, by
          rw [← pow_mul, mul_comm (j : ℕ), pow_mul,
            (zetaC_isPrimitiveRoot (Nat.mul_pos hq.pos hP₁)).pow_eq_one, one_pow]⟩)
        (hT.trans (by linarith)) (fun _ => hT)
    · -- case (iii): `q ∤ P₁`
      have hcop : q.Coprime P₁ := (Nat.Prime.coprime_iff_not_dvd hq).2 hdvd
      obtain ⟨a, ha, hdec⟩ := exists_cycInt_sum_pow_sub hq.one_lt hP₁ hcop hβ
      have hβa : β = ∑ j, a j * zetaC q ^ (j : ℕ) := by
        rw [(hdec ⟨0, hq.pos⟩).2, sum_sub_mul_zetaC_pow hq.one_lt]
      have hMa : cassM (q * P₁) (∑ j, a j * zetaC q ^ (j : ℕ)) ≤ B := hβa ▸ hM
      have h4B : 4 * B < q := by nlinarith
      obtain ⟨i₀, hi₀⟩ := cassels_majority hq hP₁ hdvd a ha hMa h4B
      obtain ⟨c, hcdef⟩ : ∃ c : Fin q → ℂ, c = fun j => a j - a i₀ := ⟨_, rfl⟩
      have hcmem : ∀ j, c j ∈ cycInt P₁ := by rw [hcdef]; exact (hdec i₀).1
      have hβc : β = ∑ j, c j * zetaC q ^ (j : ℕ) := by rw [hcdef]; exact (hdec i₀).2
      have hi₀' : (q : ℝ) <
          2 * (((univ : Finset (Fin q)).filter fun j => c j = 0).card : ℝ) := by
        rw [hcdef]; exact hi₀
      have hZX : ((univ : Finset (Fin q)).filter fun j => c j = 0).card +
          ((univ : Finset (Fin q)).filter fun j => c j ≠ 0).card = q := by
        have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin q)))
          (fun j => c j = 0)
        rw [Finset.card_univ, Fintype.card_fin] at this
        simpa only [ne_eq] using this
      have hA : ((((univ : Finset (Fin q)).filter fun j => c j = 0).card : ℝ)) *
          ∑ i, cassM P₁ (c i) ≤ ((q : ℝ) - 1) * cassM (q * P₁) β := by
        have h1 := two_mul_card_mul_sum_le (P := P₁) c
        rw [← cassels_identity_coprime hq hP₁ hdvd c
          (fun j => mem_cycField_of_mem_cycInt (hcmem j)), ← hβc] at h1
        linarith
      have hXT : ((((univ : Finset (Fin q)).filter fun j => c j ≠ 0).card : ℝ)) ≤
          ∑ i, cassM P₁ (c i) := card_filter_ne_zero_le_sum_cassM hP₁ c hcmem
      obtain ⟨hT, hT1⟩ := loxton_ineq hB hM (Finset.sum_nonneg fun i _ => cassM_nonneg _ _)
        hZX hi₀' hA hXT hq₀'
      rw [hβc]
      exact sum_mem_sumRoots_of_bounds hP₁ hB hΛge hinner houter c hcmem
        (fun j => zetaC q ^ (j : ℕ))
        (fun j => ⟨q, hq.pos, by
          rw [← pow_mul, mul_comm (j : ℕ), pow_mul, (zetaC_isPrimitiveRoot hq.pos).pow_eq_one,
            one_pow]⟩) hT hT1

/-- **Loxton's theorem, qualitative form.** For every `B` there is `Λ` such that every
cyclotomic integer of Cassels height at most `B` is a sum of at most `Λ` roots of unity. -/
theorem loxton_qualitative (B : ℝ) :
    ∃ Λ : ℕ, ∀ P, 0 < P → ∀ β ∈ cycInt P, cassM P β ≤ B → β ∈ SumRoots Λ := by
  have key : ∀ n : ℕ, ∀ B : ℝ, B ≤ n / 2 →
      ∃ Λ : ℕ, ∀ P, 0 < P → ∀ β ∈ cycInt P, cassM P β ≤ B → β ∈ SumRoots Λ := by
    intro n
    induction n with
    | zero =>
      intro B hB
      refine ⟨0, fun P hP β hβ hM => ?_⟩
      rw [eq_zero_of_cassM_lt_one hP hβ (by simp at hB; linarith)]
      exact SumRoots.zero_mem 0
    | succ n ih =>
      intro B hB
      by_cases hB1 : B < 1
      · refine ⟨0, fun P hP β hβ hM => ?_⟩
        rw [eq_zero_of_cassM_lt_one hP hβ (by linarith)]
        exact SumRoots.zero_mem 0
      · push Not at hB1
        obtain ⟨Λ', hΛ'⟩ := ih (B - 1 / 2) (by push_cast at hB; linarith)
        exact loxton_step hB1 hΛ'
  exact key ⌈2 * B⌉₊ B (by
    have := Nat.le_ceil (2 * B)
    linarith)

/-- **Corollary (Loxton).** Algebraic integers of bounded house in cyclotomic fields are sums
of a bounded number of roots of unity. -/
theorem loxton_house (B : ℝ) :
    ∃ Λ : ℕ, ∀ n, 0 < n → ∀ β ∈ cycField n, IsIntegral ℤ β → HouseLE β B → β ∈ SumRoots Λ := by
  obtain ⟨Λ, hΛ⟩ := loxton_qualitative (B ^ 2)
  refine ⟨Λ, fun n hn β hβ hint hhouse => ?_⟩
  exact hΛ n hn β ((mem_cycInt_iff hn).2 ⟨hβ, hint⟩) (cassM_le_sq_of_houseLE hn hβ hhouse)

end IngramMello
