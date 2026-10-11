import IngramMello.SuperAttracting

/-!
# Lemma 7 (high-order resultants): the algebraic core

For a monic `A` over a commutative ring `R₀`, `resM A g = Res(A, g)` is the product of `g`
over the roots of `A`. For a family `f ∈ R₀[z]` put `P_n = fⁿ` (as a polynomial in `z`) and
`W ℓ j = Res(A, f^ℓ - f^j)`.

Main results:
* `resM_mul`, `resM_map`, `resM_eq_prod_roots`: multiplicativity, specialization, and the
  product formula over `ℂ`.
* `W_succ`: the recursion `W_{q(n+1),qn} = W_{qn,q(n-1)} Q_n`.
* `W_mem_ker_pow`: if a root `c₀` of the specialization `A_ev` is a critical point of `f_ev`
  and `f_ev^q(c₀) = c₀`, then `W_{q(ℓ+1),qℓ} ∈ (ker ev)^(ℓ+1)`.
* `W_ne_zero`: `W ℓ j ≠ 0` if no root of `A` has `f^ℓ(c) = f^j(c)`.

* `isIntegrallyClosed_mvLaurent`: `R[ℤ^r]` is integrally closed for integrally closed `R`.
* `exists_infiniteOrbitFactor`: the paper's `A` (monic factor of `f'/d` whose roots are the
  infinite-orbit critical points), over any integrally closed domain.
* `isRoot_A_of_superAttracting`: the root `c₀` supplied by `SuperAttracting` (after a ring hom
  `R₀ → ℂ[t^{±1}]`) is a root of the specialization of `A`.
* `exists_infiniteOrbitFactor_monicCentred`: the same factor `A` for `f = monicCentred d a`,
  with its roots characterized as the infinite-orbit critical points.
* `exists_superAttracting_root`: the super-attracting parameter of Lemma 6, as a root of a
  specialization of `A`, using the cited `SuperAttracting` and the monomial-curve reduction
  of `SuperAttracting.lean`.
* `exists_highOrderResultant`: the assembled statement (Lemma 7 combined with Lemma 6) for
  `f = monicCentred d a` over `R₀`.
-/

namespace IngramMello

open Polynomial

section Res

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `Res(A, g)` with the natural degrees. For monic `A` this is `∏_{A(c) = 0} g(c)`. -/
noncomputable def resM (A g : R[X]) : R := resultant A g A.natDegree g.natDegree

theorem resultant_monic_of_le {A g : R[X]} (hA : A.Monic) {n : ℕ} (hn : g.natDegree ≤ n) :
    resultant A g A.natDegree n = resM A g := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [resultant_add_right_deg _ _ _ _ k le_rfl, hA.coeff_natDegree, one_pow, one_mul]
  rfl

theorem resM_mul {A : R[X]} (hA : A.Monic) (g h : R[X]) :
    resM A (g * h) = resM A g * resM A h := by
  rw [← resultant_monic_of_le hA (natDegree_mul_le (p := g) (q := h)),
    resultant_mul_right _ _ _ _ le_rfl]
  rfl

theorem resM_map {A : R[X]} (hA : A.Monic) (φ : R →+* S) [Nontrivial S] (g : R[X]) :
    φ (resM A g) = resM (A.map φ) (g.map φ) := by
  rw [resM, ← resultant_map_map, ← hA.natDegree_map φ,
    resultant_monic_of_le (hA.map φ) (natDegree_map_le)]

theorem resM_eq_prod_roots {K : Type*} [Field K] {A : K[X]} (hA : A.Monic) (hs : A.Splits)
    (g : K[X]) : resM A g = (A.roots.map g.eval).prod := by
  rw [resM, resultant_eq_prod_eval _ _ _ le_rfl hs, hA.leadingCoeff, one_pow, one_mul]

/-- If `A_φ` has a root `c` with `g_φ(c) = 0` (`φ` to an algebraically closed field), then
`φ(Res(A, g)) = 0`. -/
theorem resM_map_eq_zero {K : Type*} [Field K] [IsAlgClosed K] {A : R[X]} (hA : A.Monic)
    (φ : R →+* K) (g : R[X]) {c : K} (hc : (A.map φ).IsRoot c) (hg : (g.map φ).eval c = 0) :
    φ (resM A g) = 0 := by
  rw [resM_map hA, resM_eq_prod_roots (hA.map φ) (IsAlgClosed.splits _)]
  refine Multiset.prod_eq_zero (Multiset.mem_map.2 ⟨c, ?_, hg⟩)
  exact (mem_roots (hA.map φ).ne_zero).2 hc

/-- If `g_φ` vanishes at no root of `A_φ` (`φ` to an algebraically closed field), then
`Res(A, g) ≠ 0`. -/
theorem resM_ne_zero {K : Type*} [Field K] [IsAlgClosed K] {A : R[X]} (hA : A.Monic)
    (φ : R →+* K) (g : R[X])
    (hg : ∀ c : K, (A.map φ).IsRoot c → (g.map φ).eval c ≠ 0) : resM A g ≠ 0 := by
  intro h0
  have h1 := resM_map hA φ g
  rw [h0, map_zero, resM_eq_prod_roots (hA.map φ) (IsAlgClosed.splits _)] at h1
  obtain ⟨y, hy, hy0⟩ := Multiset.mem_map.1 (Multiset.prod_eq_zero_iff.1 h1.symm)
  exact hg y ((mem_roots (hA.map φ).ne_zero).1 hy) hy0

end Res

section DividedDifference

variable {R : Type*} [CommRing R]

/-- The divided difference `(G(a) - G(b)) / (a - b)`, written as a polynomial expression in
`a` and `b`. -/
noncomputable def divDiff (G a b : R[X]) : R[X] :=
  G.sum fun i c => C c * ∑ j ∈ Finset.range i, a ^ j * b ^ (i - 1 - j)

theorem comp_sub_comp (G a b : R[X]) : G.comp a - G.comp b = (a - b) * divDiff G a b := by
  rw [comp_eq_sum_left, comp_eq_sum_left, divDiff, Polynomial.sum, Polynomial.sum,
    Polynomial.sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_sub, ← (Commute.all a b).geom_sum₂_mul]
  ring

/-- Under a ring hom sending `a` and `b` to the same value `c`, the divided difference
becomes the derivative `G'(c)`. -/
theorem divDiff_eval₂ {K : Type*} [CommRing K] (φ : R →+* K) (G a b : R[X]) (c : K)
    (ha : a.eval₂ φ c = c) (hb : b.eval₂ φ c = c) :
    (divDiff G a b).eval₂ φ c = (G.map φ).derivative.eval c := by
  rw [derivative_map, eval_map, derivative_apply, divDiff, Polynomial.sum, Polynomial.sum,
    eval₂_finsetSum, eval₂_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eval₂_mul, eval₂_C, eval₂_finsetSum, eval₂_pow, ha, hb, eval₂_X, geom_sum₂_self,
    eval₂_natCast, map_mul, map_natCast]
  ring

end DividedDifference

section Iterates

variable {R S : Type*} [CommRing R] [CommRing S]

/-- `P f n = fⁿ(z)` as a polynomial. -/
noncomputable def P (f : R[X]) (n : ℕ) : R[X] := f.comp^[n] X

theorem P_add (f : R[X]) (m n : ℕ) : P f (m + n) = (P f m).comp (P f n) := by
  induction m with
  | zero => simp [P]
  | succ m ih =>
    simp only [P] at ih ⊢
    rw [Nat.succ_add, Function.iterate_succ_apply', Function.iterate_succ_apply', ih,
      comp_assoc]

theorem P_mul (f : R[X]) (q n : ℕ) : P f (q * n) = (P f q).comp^[n] X := by
  induction n with
  | zero => simp [P]
  | succ n ih => rw [Nat.mul_succ, add_comm, P_add, ih, Function.iterate_succ_apply']

theorem eval_P (f : R[X]) (n : ℕ) (c : R) :
    (P f n).eval c = (fun z => f.eval z)^[n] c := by
  simp [P]

theorem map_P (φ : R →+* S) (f : R[X]) (n : ℕ) : (P f n).map φ = P (f.map φ) n := by
  induction n with
  | zero => simp [P]
  | succ n ih => rw [P, Function.iterate_succ_apply', ← P, map_comp, ih, P, P,
      Function.iterate_succ_apply']

/-- If `c` is a critical point of `f` then it is a critical point of `fⁿ`, `n ≥ 1`. -/
theorem derivative_P_eval_eq_zero (f : R[X]) {n : ℕ} (hn : 0 < n) {c : R}
    (hc : f.derivative.eval c = 0) : (P f n).derivative.eval c = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [add_comm, P_add, show P f 1 = f by simp [P], derivative_comp,
    eval_mul, hc, zero_mul]

end Iterates

section HighOrderResultants

variable {R₀ : Type*} [CommRing R₀]

/-- `W_{ℓ,j} = Res(A, f^ℓ - f^j)`. -/
noncomputable def W (A f : R₀[X]) (l j : ℕ) : R₀ := resM A (P f l - P f j)

/-- The factor `Q_n = Res(A, H(g^n, g^{n-1}))`, `g = f^q`, indexed so that `Q q f n = Q_{n+1}`. -/
noncomputable def Q (A f : R₀[X]) (q n : ℕ) : R₀ :=
  resM A (divDiff (P f q) (P f (q * (n + 1))) (P f (q * n)))

/-- **Lemma 7, recursion.** `W_{q(n+2),q(n+1)} = W_{q(n+1),qn} Q_{n+1}`. -/
theorem W_succ {A : R₀[X]} (hA : A.Monic) (f : R₀[X]) (q n : ℕ) :
    W A f (q * (n + 2)) (q * (n + 1)) = W A f (q * (n + 1)) (q * n) * Q A f q n := by
  rw [W, W, Q, ← resM_mul hA, ← comp_sub_comp, P_mul, P_mul, P_mul,
    Function.iterate_succ_apply', Function.iterate_succ_apply' (f := (P f q).comp)]

variable {K : Type*} [Field K] [IsAlgClosed K]

/-- **Lemma 7, order estimate.** Let `ev : R₀ → K` (algebraically closed) and suppose some root
`c₀` of `A_ev` is a critical point of `f_ev` with `f_ev^q(c₀) = c₀`, `q ≥ 1`. Then
`W_{q(ℓ+1),qℓ} ∈ (ker ev)^(ℓ+1)`. -/
theorem W_mem_ker_pow {A : R₀[X]} (hA : A.Monic) (f : R₀[X]) (ev : R₀ →+* K) {q : ℕ}
    (hq : 0 < q) {c₀ : K} (hA₀ : (A.map ev).IsRoot c₀)
    (hcrit : (f.map ev).derivative.eval c₀ = 0)
    (hper : (fun z => (f.map ev).eval z)^[q] c₀ = c₀) (l : ℕ) :
    W A f (q * (l + 1)) (q * l) ∈ RingHom.ker ev ^ (l + 1) := by
  have hfix : ∀ n, (P f (q * n)).eval₂ ev c₀ = c₀ := fun n => by
    rw [eval₂_eq_eval_map, map_P, eval_P, Function.iterate_mul, Function.iterate_fixed hper]
  induction l with
  | zero =>
    have h1 := hfix 1
    have h0 := hfix 0
    rw [mul_one] at h1
    rw [mul_zero] at h0
    simp only [zero_add, pow_one, mul_one, mul_zero, RingHom.mem_ker, W]
    refine resM_map_eq_zero hA ev _ hA₀ ?_
    rw [eval_map, eval₂_sub, h1, h0, sub_self]
  | succ l ih =>
    rw [show l + 1 + 1 = l + 2 by ring, W_succ hA, pow_succ]
    refine Ideal.mul_mem_mul ih ?_
    rw [RingHom.mem_ker, Q]
    refine resM_map_eq_zero hA ev _ hA₀ ?_
    rw [eval_map, divDiff_eval₂ ev _ _ _ _ (hfix _) (hfix _), map_P]
    exact derivative_P_eval_eq_zero _ hq hcrit

/-- **Lemma 7, nonvanishing.** If for some `ι : R₀ → K` no root `c` of `A_ι` satisfies
`f^ℓ(c) = f^j(c)`, then `W_{ℓ,j} ≠ 0`. -/
theorem W_ne_zero {A : R₀[X]} (hA : A.Monic) (f : R₀[X]) (ι : R₀ →+* K) (l j : ℕ)
    (h : ∀ c : K, (A.map ι).IsRoot c →
      (fun z => (f.map ι).eval z)^[l] c ≠ (fun z => (f.map ι).eval z)^[j] c) :
    W A f l j ≠ 0 := by
  refine resM_ne_zero hA ι _ fun c hc => ?_
  rw [Polynomial.map_sub, eval_sub, map_P, map_P, eval_P, eval_P, sub_ne_zero]
  exact h c hc

/-- The specialization formula: `ev W_{ℓ,j} = ∏_{A_ev(c) = 0} (f_ev^ℓ(c) - f_ev^j(c))`, with
multiplicity. -/
theorem ev_W {A : R₀[X]} (hA : A.Monic) (f : R₀[X]) (ev : R₀ →+* K) (l j : ℕ) :
    ev (W A f l j) = ((A.map ev).roots.map fun c =>
      (fun z => (f.map ev).eval z)^[l] c - (fun z => (f.map ev).eval z)^[j] c).prod := by
  rw [W, resM_map hA, resM_eq_prod_roots (hA.map ev) (IsAlgClosed.splits _)]
  congr 1
  refine Multiset.map_congr rfl fun c _ => ?_
  rw [Polynomial.map_sub, eval_sub, map_P, map_P, eval_P, eval_P]

/-- **Lemma 7, order estimate on the torus.** Let `ι : R₀ → ℂ[u^{±1}]` and `x ∈ (ℂ^×)^r`. If
some root `c₀` of `A_x` is a critical point of `f_x` with `f_x^q(c₀) = c₀`, `q ≥ 1`, then
`ord_x ι(W_{q(ℓ+1),qℓ}) ≥ ℓ + 1`. -/
theorem map_W_mem_maxIdeal_pow {r : ℕ} {A : R₀[X]} (hA : A.Monic) (f : R₀[X])
    (ι : R₀ →+* MvLaurent r) (x : Fin r → ℂˣ) {q : ℕ} (hq : 0 < q) {c₀ : ℂ}
    (hA₀ : (A.map (((MvLaurent.evalHom x : MvLaurent r →+* ℂ)).comp ι)).IsRoot c₀)
    (hcrit : (f.map ((MvLaurent.evalHom x : MvLaurent r →+* ℂ).comp ι)).derivative.eval c₀ = 0)
    (hper : (fun z => (f.map ((MvLaurent.evalHom x : MvLaurent r →+* ℂ).comp ι)).eval z)^[q] c₀
      = c₀) (l : ℕ) :
    ι (W A f (q * (l + 1)) (q * l)) ∈ MvLaurent.maxIdeal x ^ (l + 1) := by
  have h := Ideal.mem_map_of_mem ι (W_mem_ker_pow hA f _ hq hA₀ hcrit hper l)
  rw [Ideal.map_pow] at h
  refine Ideal.pow_right_mono ?_ _ h
  rw [Ideal.map_le_iff_le_comap]
  intro y hy
  simpa [MvLaurent.maxIdeal, RingHom.mem_ker] using hy

end HighOrderResultants

/-! ### The Laurent polynomial ring is integrally closed -/

section IntClosed

open AddMonoidAlgebra

theorem isIntegrallyClosed_laurentPolynomial (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed (LaurentPolynomial R) :=
  isIntegrallyClosed_of_isLocalization (R := Polynomial R) _ (Submonoid.powers Polynomial.X)
    (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)

theorem isIntegrallyClosed_mvLaurent (R : Type*) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : ∀ r : ℕ, IsIntegrallyClosed (AddMonoidAlgebra R (Fin r → ℤ))
  | 0 => by
    refine IsIntegrallyClosed.of_equiv (RingEquiv.ofBijective
      (algebraMap R (AddMonoidAlgebra R (Fin 0 → ℤ))) ⟨?_, fun x => ⟨x.coeff 0, ?_⟩⟩)
    · intro a b h
      have := congrArg (fun y : AddMonoidAlgebra R (Fin 0 → ℤ) => y.coeff 0) h
      simpa using this
    · refine AddMonoidAlgebra.ext (Finsupp.ext fun m => ?_)
      rw [Subsingleton.elim m 0]
      simp
  | r + 1 => by
    have := isIntegrallyClosed_mvLaurent R r
    have : IsIntegrallyClosed (AddMonoidAlgebra (AddMonoidAlgebra R (Fin r → ℤ)) ℤ) :=
      isIntegrallyClosed_laurentPolynomial _
    let e : (ℤ × (Fin r → ℤ)) ≃+ (Fin (r + 1) → ℤ) :=
      (Fin.consLinearEquiv ℤ (fun _ : Fin (r + 1) => ℤ)).toAddEquiv
    exact IsIntegrallyClosed.of_equiv
      (curryRingEquiv.symm.trans (domCongr R R e).toRingEquiv)

end IntClosed

/-! ### The factor `A` of `f'/d` carrying the infinite-orbit critical points -/

section InfiniteOrbitFactor

open UniqueFactorizationMonoid

/-- If `F^[l] c = F^[j] c` with `l ≠ j`, the forward orbit of `c` is finite. -/
theorem finite_orbit_of_iterate_eq {α : Type*} (F : α → α) {c : α} {l j : ℕ} (hlj : l ≠ j)
    (h : F^[l] c = F^[j] c) : (Set.range fun n => F^[n] c).Finite := by
  wlog hjl : j < l generalizing l j
  · exact this hlj.symm h.symm (lt_of_le_of_ne (not_lt.1 hjl) hlj)
  classical
  refine ((Finset.range l).image fun n => F^[n] c).finite_toSet.subset ?_
  rintro _ ⟨n, rfl⟩
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < l
    · exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨n, Finset.mem_range.2 hn, rfl⟩)
    · have : F^[n] c = F^[n - l + j] c := by
        rw [Function.iterate_add_apply, ← h, ← Function.iterate_add_apply,
          Nat.sub_add_cancel (not_lt.1 hn)]
      change F^[n] c ∈ _
      rw [this]
      exact ih _ (by omega)

/-- Finitely many points with finite orbits have a common pair `n ≠ m` with `F^n = F^m`. -/
theorem exists_iterate_eq_of_finite {α : Type*} (F : α → α) (S : Finset α)
    (hS : ∀ c ∈ S, (Set.range fun n => F^[n] c).Finite) :
    ∃ n m : ℕ, n ≠ m ∧ ∀ c ∈ S, F^[n] c = F^[m] c := by
  have hfin : (Set.pi Set.univ fun c : S => Set.range fun n => F^[n] (c : α)).Finite :=
    Set.Finite.pi fun c => hS c c.2
  obtain ⟨n, -, m, -, hnm, h⟩ := Set.infinite_univ.exists_ne_map_eq_of_mapsTo
    (f := fun n : ℕ => fun c : S => F^[n] (c : α))
    (fun n _ => Set.mem_univ_pi.2 fun c => Set.mem_range_self n) hfin
  exact ⟨n, m, hnm, fun c hc => congrFun h ⟨c, hc⟩⟩

theorem multiset_prod_dvd_pow {M : Type*} [CommMonoid M] (s : Multiset M) (a : M)
    (h : ∀ x ∈ s, x ∣ a) : s.prod ∣ a ^ Multiset.card s := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons x s ih =>
    rw [Multiset.prod_cons, Multiset.card_cons, pow_succ']
    exact mul_dvd_mul (h x (Multiset.mem_cons_self _ _))
      (ih fun y hy => h y (Multiset.mem_cons_of_mem hy))



theorem isCoprime_multiset_prod_left {R : Type*} [CommRing R] (s : Multiset R) (h : R)
    (hs : ∀ p ∈ s, IsCoprime p h) : IsCoprime s.prod h := by
  induction s using Multiset.induction_on with
  | empty => exact isCoprime_one_left
  | cons x s ih =>
    rw [Multiset.prod_cons]
    exact (hs x (Multiset.mem_cons_self _ _)).mul_left
      (ih fun y hy => hs y (Multiset.mem_cons_of_mem hy))

/-- Split a monic `g` over a field into a monic factor coprime to `h` and a monic factor
dividing a power of `h`. -/
theorem exists_coprime_split {K : Type*} [Field K] (g h : K[X]) (hg : g.Monic) :
    ∃ A B : K[X], A.Monic ∧ B.Monic ∧ g = A * B ∧ IsCoprime A h ∧ ∃ N : ℕ, B ∣ h ^ N := by
  classical
  have hmon : ∀ p ∈ normalizedFactors g, p.Monic := fun p hp => by
    rw [← normalize_normalized_factor p hp]
    exact monic_normalize (ne_zero_of_mem_normalizedFactors hp)
  let s := normalizedFactors g
  refine ⟨(s.filter fun p => IsCoprime p h).prod, (s.filter fun p => ¬ IsCoprime p h).prod,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa using monic_multiset_prod_of_monic _ id fun p hp =>
      hmon p (Multiset.mem_of_mem_filter hp)
  · simpa using monic_multiset_prod_of_monic _ id fun p hp =>
      hmon p (Multiset.mem_of_mem_filter hp)
  · rw [Multiset.prod_filter_mul_prod_filter_not]
    refine (eq_of_monic_of_associated ?_ hg (prod_normalizedFactors hg.ne_zero)).symm
    simpa using monic_multiset_prod_of_monic _ id hmon
  · exact isCoprime_multiset_prod_left _ _ fun p hp => (Multiset.mem_filter.1 hp).2
  · refine ⟨_, multiset_prod_dvd_pow _ _ fun p hp => ?_⟩
    obtain ⟨hp, hc⟩ := Multiset.mem_filter.1 hp
    exact not_not.1 fun hd => hc ((irreducible_of_normalized_factor p hp).coprime_iff_not_dvd.2 hd)

variable {R₀ : Type*} [CommRing R₀] [IsDomain R₀] [IsIntegrallyClosed R₀]

/-- **Construction of `A`** (proof of Lemma 7). Let `R₀` be an integrally closed domain,
`L` an algebraic closure of its fraction field, and `g ∈ R₀[z]` monic (later `g = f'/d`).
Then `g = A B` with `A, B` monic in `R₀[z]`, every root of `A` in `L` has infinite forward
orbit under `f`, and `B ∣ (fⁿ - fᵐ)^N` for some `n ≠ m`. -/
theorem exists_infiniteOrbitFactor (f g : R₀[X]) (hg : g.Monic) :
    ∃ (A B : R₀[X]) (n m N : ℕ), A.Monic ∧ B.Monic ∧ g = A * B ∧ n ≠ m ∧
      B ∣ (P f n - P f m) ^ N ∧
      ∀ c : AlgebraicClosure (FractionRing R₀),
        (A.map ((algebraMap (FractionRing R₀) _).comp (algebraMap R₀ _))).IsRoot c →
        ¬ (Set.range fun k => (fun z => (f.map ((algebraMap (FractionRing R₀) _).comp
          (algebraMap R₀ _))).eval z)^[k] c).Finite := by
  classical
  set F0 := FractionRing R₀
  set L := AlgebraicClosure F0
  set ι : R₀ →+* L := (algebraMap F0 L).comp (algebraMap R₀ F0)
  set Fι := fun z => (f.map ι).eval z
  have hinj : Function.Injective (algebraMap R₀ F0) := IsFractionRing.injective R₀ F0
  obtain ⟨n, m, hnm, hS⟩ := exists_iterate_eq_of_finite Fι
    ((g.map ι).roots.toFinset.filter fun c => (Set.range fun k => Fι^[k] c).Finite)
    fun c hc => (Finset.mem_filter.1 hc).2
  set h := P f n - P f m
  obtain ⟨A0, B0, hA0, hB0, hgAB, hcop, N, hBN⟩ :=
    exists_coprime_split (g.map (algebraMap R₀ F0)) (h.map (algebraMap R₀ F0)) (hg.map _)
  obtain ⟨A, hA⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F0 hg (Dvd.intro B0 hgAB.symm)
  obtain ⟨B, hB⟩ := IsIntegrallyClosed.eq_map_mul_C_of_dvd F0 hg (Dvd.intro_left A0 hgAB.symm)
  rw [hA0.leadingCoeff, C_1, mul_one] at hA
  rw [hB0.leadingCoeff, C_1, mul_one] at hB
  have hAm : A.Monic := by
    rw [Monic, ← hinj.eq_iff, ← leadingCoeff_map_of_injective hinj, hA, hA0.leadingCoeff,
      map_one]
  have hBm : B.Monic := by
    rw [Monic, ← hinj.eq_iff, ← leadingCoeff_map_of_injective hinj, hB, hB0.leadingCoeff,
      map_one]
  have hgAB' : g = A * B := map_injective _ hinj (by rw [Polynomial.map_mul, hA, hB, hgAB])
  refine ⟨A, B, n, m, N, hAm, hBm, hgAB', hnm, ?_, fun c hc hfin => ?_⟩
  · rw [← map_dvd_map _ hinj hBm, Polynomial.map_pow, hB]
    exact hBN
  · -- `h(c) ≠ 0` since `A` is coprime to `h`
    have hAι : A.map ι = A0.map (algebraMap F0 L) := by rw [← hA, map_map]
    have hhι : h.map ι = (h.map (algebraMap R₀ F0)).map (algebraMap F0 L) := by rw [map_map]
    obtain ⟨u, v, huv⟩ := hcop.map (mapRingHom (algebraMap F0 L))
    have h1 := congrArg (eval c) huv
    simp only [coe_mapRingHom, eval_add, eval_mul, eval_one, ← hAι, hc.eq_zero, mul_zero,
      zero_add, ← hhι] at h1
    -- but `c` is a root of `g`, so it has `fⁿ(c) = fᵐ(c)`
    have hcg : c ∈ (g.map ι).roots := by
      rw [mem_roots (hg.map ι).ne_zero, IsRoot, hgAB', Polynomial.map_mul, eval_mul,
        hc.eq_zero, zero_mul]
    have := hS c (Finset.mem_filter.2 ⟨Multiset.mem_toFinset.2 hcg, hfin⟩)
    rw [Polynomial.map_sub, eval_sub, map_P, map_P, eval_P, eval_P, this, sub_self,
      mul_zero] at h1
    exact zero_ne_one h1

omit [IsDomain R₀] [IsIntegrallyClosed R₀] in
/-- The factor `A` catches every root of `g` whose orbit meets no relation `fⁿ = fᵐ`: under any
ring hom `ψ` to a domain, a root `c` of `g_ψ` with `f_ψⁿ(c) ≠ f_ψᵐ(c)` is a root of `A_ψ`. -/
theorem isRoot_of_iterate_ne {S : Type*} [CommRing S] [IsDomain S] {f g A B : R₀[X]}
    {n m N : ℕ} (hgAB : g = A * B) (hB : B ∣ (P f n - P f m) ^ N) (ψ : R₀ →+* S) {c : S}
    (hc : (g.map ψ).IsRoot c)
    (hnm : (fun z => (f.map ψ).eval z)^[n] c ≠ (fun z => (f.map ψ).eval z)^[m] c) :
    (A.map ψ).IsRoot c := by
  rw [hgAB, Polynomial.map_mul, IsRoot, eval_mul] at hc
  refine (mul_eq_zero.1 hc).resolve_right fun hBc => hnm ?_
  obtain ⟨k, hk⟩ := hB
  have := congrArg (fun p => (p.map ψ).eval c) hk
  simp only [Polynomial.map_pow, Polynomial.map_mul, eval_pow, eval_mul, hBc, zero_mul,
    Polynomial.map_sub, eval_sub, map_P, eval_P] at this
  exact sub_eq_zero.1 (pow_eq_zero_iff'.1 this).1

end InfiniteOrbitFactor

/-! ### Glue with `SuperAttracting` -/

/-- Over an algebraically closed field, a monic `p` whose roots are all roots of `q` divides
`q ^ deg p`. -/
theorem dvd_pow_of_roots {K : Type*} [Field K] [IsAlgClosed K] {p q : K[X]} (hp : p.Monic)
    (h : ∀ c, p.IsRoot c → q.IsRoot c) : p ∣ q ^ p.natDegree := by
  rw [(IsAlgClosed.splits p).natDegree_eq_card_roots, ← Multiset.card_map (fun a => X - C a)]
  nth_rw 1 [(IsAlgClosed.splits p).eq_prod_roots_of_monic hp]
  refine multiset_prod_dvd_pow _ _ fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.1 hx
  exact dvd_iff_isRoot.2 (h a (isRoot_of_mem_roots ha))


/-- **Glue between `SuperAttracting` and `A`.** Let `g = A B` with `B ∣ (fⁿ - fᵐ)^N`, `n ≠ m`,
and `f' = d g`. Let `ψ : R₀ → ℂ[t^{±1}]` and let `P` be a monic polynomial over `ℂ[t^{±1}]`
whose roots in `\overline{ℂ(t)}` are critical points of `f_ψ` with infinite orbit. Then every
root `c₀` of a specialization `P_{t₀}` is a root of `A_{t₀}`. -/
theorem isRoot_A_of_superAttracting {R₀ : Type*} [CommRing R₀] {f g A B : R₀[X]}
    {n m N : ℕ} (hnm : n ≠ m) (hgAB : g = A * B) (hB : B ∣ (P f n - P f m) ^ N)
    {d : ℕ} (hd : d ≠ 0) (hfg : derivative f = C (d : R₀) * g)
    (ψ : R₀ →+* LaurentPolynomial ℂ) (Pp : (LaurentPolynomial ℂ)[X]) (hPm : Pp.Monic)
    (hroots : ∀ c : GenericField, aeval c Pp = 0 →
      aeval c (derivative (f.map ψ)) = 0 ∧ ¬ HasFiniteOrbit (f.map ψ) c)
    (t₀ : ℂˣ) {c₀ : ℂ}
    (hc₀ : (Pp.map (LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀)).IsRoot c₀) :
    (A.map ((LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀).comp ψ)).IsRoot c₀ := by
  have hj : Function.Injective (algebraMap (LaurentPolynomial ℂ) GenericField) := by
    rw [IsScalarTower.algebraMap_eq (LaurentPolynomial ℂ)
      (FractionRing (LaurentPolynomial ℂ)) GenericField]
    exact (algebraMap (FractionRing (LaurentPolynomial ℂ)) GenericField).injective.comp
      (IsFractionRing.injective _ _)
  set j := algebraMap (LaurentPolynomial ℂ) GenericField
  have : CharZero GenericField :=
    charZero_of_injective_ringHom (j.comp LaurentPolynomial.C).injective
  have hF : (fun w : GenericField => aeval w (f.map ψ)) =
      fun z => (f.map (j.comp ψ)).eval z := by
    funext w; rw [aeval_def, eval₂_eq_eval_map, map_map]
  have key : ∀ c, (Pp.map j).IsRoot c → ((A.map ψ).map j).IsRoot c := by
    intro c hc
    obtain ⟨hcrit, horb⟩ := hroots c (by rwa [aeval_def, eval₂_eq_eval_map])
    rw [map_map]
    refine isRoot_of_iterate_ne hgAB hB (j.comp ψ) ?_ fun heq => horb ?_
    · rw [aeval_def, eval₂_eq_eval_map, derivative_map, map_map, hfg,
        Polynomial.map_mul, eval_mul, map_C, eval_C, map_natCast] at hcrit
      exact (mul_eq_zero.1 hcrit).resolve_left (Nat.cast_ne_zero.2 hd)
    · unfold HasFiniteOrbit
      rw [hF]
      exact finite_orbit_of_iterate_eq _ hnm heq
  have h1 := dvd_pow_of_roots (hPm.map j) key
  rw [← Polynomial.map_pow, map_dvd_map j hj hPm] at h1
  have h2 := Polynomial.map_dvd (LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀) h1
  rw [Polynomial.map_pow, map_map] at h2
  obtain ⟨k, hk⟩ := h2
  have := congrArg (eval c₀) hk
  rw [eval_mul, hc₀.eq_zero, zero_mul, eval_pow] at this
  exact pow_eq_zero_iff'.1 this |>.1

/-! ### Lemmas 6 and 7 for monic centred families -/

theorem map_monicCentred {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ)
    (a : Fin (d - 1) → R) : (monicCentred d a).map φ = monicCentred d (fun i => φ (a i)) := by
  simp [monicCentred, Polynomial.map_sum]

/-- `f' = d · g` with `g` monic of degree `d - 1`, over a `ℚ`-algebra. -/
theorem exists_derivative_monicCentred {R : Type*} [CommRing R] [Algebra ℚ R] [Nontrivial R]
    {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R) :
    ∃ g : R[X], g.Monic ∧ g.natDegree = d - 1 ∧ derivative (monicCentred d a) = C (d : R) * g := by
  set S := ∑ i : Fin (d - 1), C (a i) * X ^ (i : ℕ)
  set e : R := algebraMap ℚ R (d : ℚ)⁻¹
  have hde : (d : R) * e = 1 := by
    rw [← map_natCast (algebraMap ℚ R), ← map_mul, mul_inv_cancel₀ (by exact_mod_cast
      (show d ≠ 0 by omega)), map_one]
  have hS : S.natDegree ≤ d - 2 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)
  have hdeg : (C e * derivative S).degree < ((d - 1 : ℕ) : WithBot ℕ) := by
    have h1 : (C e * derivative S).natDegree < d - 1 := by
      have := (natDegree_C_mul_le e (derivative S)).trans (natDegree_derivative_le S)
      omega
    exact (degree_le_natDegree).trans_lt (by exact_mod_cast h1)
  refine ⟨X ^ (d - 1) + C e * derivative S, monic_X_pow_add hdeg, ?_, ?_⟩
  · rw [natDegree_add_eq_left_of_degree_lt (by rwa [degree_X_pow]), natDegree_X_pow]
  · rw [monicCentred, derivative_add, derivative_X_pow, mul_add, ← mul_assoc, ← C_mul, hde,
      C_1, one_mul]

/-- Evaluation in the algebraic closure `L` of `Frac R₀`: `aeval c p` is the value at `c` of `p`
mapped along `R₀ → Frac R₀ → L`. -/
theorem aeval_eq_eval_map_algebraicClosure {R₀ : Type*} [CommRing R₀] [IsDomain R₀] (p : R₀[X])
    (c : AlgebraicClosure (FractionRing R₀)) :
    aeval c p = (p.map ((algebraMap (FractionRing R₀) (AlgebraicClosure (FractionRing R₀))).comp
      (algebraMap R₀ (FractionRing R₀)))).eval c := by
  rw [aeval_def, eval₂_eq_eval_map,
    IsScalarTower.algebraMap_eq R₀ (FractionRing R₀) (AlgebraicClosure (FractionRing R₀))]

/-- `HasFiniteOrbit` in the algebraic closure of `Frac R₀`, in terms of `eval` of the mapped
polynomial. -/
theorem hasFiniteOrbit_iff_algebraicClosure {R₀ : Type*} [CommRing R₀] [IsDomain R₀] (f : R₀[X])
    (c : AlgebraicClosure (FractionRing R₀)) :
    HasFiniteOrbit f c ↔ (Set.range fun k => (fun z => (f.map
      ((algebraMap (FractionRing R₀) (AlgebraicClosure (FractionRing R₀))).comp
        (algebraMap R₀ (FractionRing R₀)))).eval z)^[k] c).Finite := by
  have h : (fun w : AlgebraicClosure (FractionRing R₀) => aeval w f) = fun z => (f.map
      ((algebraMap (FractionRing R₀) (AlgebraicClosure (FractionRing R₀))).comp
        (algebraMap R₀ (FractionRing R₀)))).eval z :=
    funext fun w => aeval_eq_eval_map_algebraicClosure f w
  unfold HasFiniteOrbit
  rw [h]

/-- **The factor `A` of `f'` for a monic centred family** (proof of Lemma 7). Over an integrally
closed `ℚ`-algebra domain `R₀`, `f' = d · A · B` with `A, B` monic, the roots of `A` in the
algebraic closure of `Frac R₀` are exactly the critical points of `f` with infinite forward
orbit, and `B ∣ (fⁿ - fᵐ)^N` for some `n ≠ m`. -/
theorem exists_infiniteOrbitFactor_monicCentred {R₀ : Type*} [CommRing R₀] [IsDomain R₀]
    [IsIntegrallyClosed R₀] [Algebra ℚ R₀] {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R₀) :
    ∃ (A B : R₀[X]) (n m N : ℕ), A.Monic ∧ B.Monic ∧
      derivative (monicCentred d a) = C (d : R₀) * (A * B) ∧ n ≠ m ∧
      B ∣ (P (monicCentred d a) n - P (monicCentred d a) m) ^ N ∧
      ∀ c : AlgebraicClosure (FractionRing R₀), aeval c A = 0 ↔
        (aeval c (derivative (monicCentred d a)) = 0 ∧
          ¬ HasFiniteOrbit (monicCentred d a) c) := by
  obtain ⟨g, hgm, -, hfg⟩ := exists_derivative_monicCentred hd a
  set f := monicCentred d a
  obtain ⟨A, B, n, m, N, hAm, hBm, hgAB, hnm, hBN, hinf⟩ := exists_infiniteOrbitFactor f g hgm
  refine ⟨A, B, n, m, N, hAm, hBm, by rw [hfg, hgAB], hnm, hBN, fun c => ?_⟩
  have : CharZero (AlgebraicClosure (FractionRing R₀)) :=
    charZero_of_injective_ringHom
      ((algebraMap R₀ (AlgebraicClosure (FractionRing R₀))).comp (algebraMap ℚ R₀)).injective
  have hd0 : (d : AlgebraicClosure (FractionRing R₀)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  rw [aeval_eq_eval_map_algebraicClosure, aeval_eq_eval_map_algebraicClosure,
    hasFiniteOrbit_iff_algebraicClosure]
  set ι' : R₀ →+* AlgebraicClosure (FractionRing R₀) :=
    (algebraMap (FractionRing R₀) (AlgebraicClosure (FractionRing R₀))).comp
      (algebraMap R₀ (FractionRing R₀))
  have hdg : ((derivative f).map ι').eval c = (d : AlgebraicClosure (FractionRing R₀)) *
      (g.map ι').eval c := by
    rw [hfg, Polynomial.map_mul, eval_mul, map_C, eval_C, map_natCast]
  constructor
  · intro hA
    refine ⟨?_, hinf c hA⟩
    rw [hdg, hgAB, Polynomial.map_mul, eval_mul, hA, zero_mul, mul_zero]
  · rintro ⟨hc, horb⟩
    rw [hdg] at hc
    have hcg : (g.map ι').IsRoot c := (mul_eq_zero.1 hc).resolve_left hd0
    exact isRoot_of_iterate_ne hgAB hBN ι' hcg fun heq =>
      horb (finite_orbit_of_iterate_eq _ hnm heq)

/-- **Super-attracting parameters for `A`** (Lemma 6 in the form used in Lemma 7). Let
`ι : R₀ → ℂ[u^{±1}]` with some `ι(a_i)` non-constant, `f = monicCentred d a`, `f' = d g` and
`g = A B` with `B ∣ (fⁿ - fᵐ)^N`, `n ≠ m`. Then, by the cited `SuperAttracting` applied along a
generic monomial curve, there are `x ∈ (ℂ^×)^r`, `q ≥ 1` and a root `c₀` of `A_x` which is a
critical point of `f_x` with `f_x^q(c₀) = c₀`. -/
theorem exists_superAttracting_root (hSA : SuperAttracting) {R₀ : Type*} [CommRing R₀]
    {r : ℕ} (ι : R₀ →+* MvLaurent r) {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R₀)
    (hnc : ∃ i, MvLaurent.NonConst (ι (a i))) {g A B : R₀[X]} {n m N : ℕ} (hnm : n ≠ m)
    (hgAB : g = A * B) (hBN : B ∣ (P (monicCentred d a) n - P (monicCentred d a) m) ^ N)
    (hfg : derivative (monicCentred d a) = C (d : R₀) * g) :
    ∃ (x : Fin r → ℂˣ) (c₀ : ℂ) (q : ℕ), 0 < q ∧
      (A.map ((MvLaurent.evalHom x : MvLaurent r →+* ℂ).comp ι)).IsRoot c₀ ∧
      ((monicCentred d a).map
        ((MvLaurent.evalHom x : MvLaurent r →+* ℂ).comp ι)).derivative.eval c₀ = 0 ∧
      (fun z => ((monicCentred d a).map
        ((MvLaurent.evalHom x : MvLaurent r →+* ℂ).comp ι)).eval z)^[q] c₀ = c₀ := by
  set f := monicCentred d a
  obtain ⟨β, hβ⟩ := MvLaurent.exists_curve_not_const (fun i => ι (a i))
  set ψ : R₀ →+* LaurentPolynomial ℂ := (MvLaurent.curve β : MvLaurent r →+* _).comp ι
  obtain ⟨i, hi⟩ := hnc
  obtain ⟨Pp, hPm, hroots, t₀, c₀, q, hq, hc₀, hper⟩ :=
    hSA d hd (fun i => ψ (a i)) ⟨i, hβ i hi⟩
  have hfψ : f.map ψ = monicCentred d (fun i => ψ (a i)) := map_monicCentred ψ d a
  rw [← hfψ] at hroots hper
  have hroot := isRoot_A_of_superAttracting hnm hgAB hBN (by omega : d ≠ 0) hfg ψ Pp hPm
    hroots t₀ hc₀
  set x : Fin r → ℂˣ := fun j => t₀ ^ β j
  have hev : (LaurentPolynomial.eval₂ (RingHom.id ℂ) t₀).comp ψ =
      (MvLaurent.evalHom x : MvLaurent r →+* ℂ).comp ι :=
    RingHom.ext fun y => MvLaurent.eval₂_curve β t₀ (ι y)
  rw [hev] at hroot
  rw [map_map, hev] at hper
  refine ⟨x, c₀, q, hq, hroot, ?_, hper⟩
  have hdvd : A ∣ derivative f := ⟨C (d : R₀) * B, by rw [hfg, hgAB]; ring⟩
  obtain ⟨k, hk⟩ := hdvd
  rw [derivative_map, hk, Polynomial.map_mul, eval_mul, hroot.eq_zero, zero_mul]

/-- **Lemma 7 combined with Lemma 6.** Let `R₀` be an integrally closed `ℚ`-algebra domain with a
ring hom `ι : R₀ → ℂ[u_1^{±1}, …, u_r^{±1}]` (in the application `R₀ = K'[ℤ^r]`), and let
`f = monicCentred d a` with `a_i ∈ R₀`, some `ι(a_i)` non-constant. Then there is a monic
`A ∣ f'` over `R₀` such that:
* `W_{ℓ,j} = Res(A, f^ℓ - f^j) ≠ 0` for `ℓ ≠ j`;
* for some `x ∈ (ℂ^×)^r` and `q ≥ 1`, `ord_x ι(W_{q(ℓ+1),qℓ}) ≥ ℓ + 1` for all `ℓ`. -/
theorem exists_highOrderResultant (hSA : SuperAttracting) {R₀ : Type*} [CommRing R₀]
    [IsDomain R₀] [IsIntegrallyClosed R₀] [Algebra ℚ R₀] {r : ℕ} (ι : R₀ →+* MvLaurent r)
    {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R₀) (hnc : ∃ i, MvLaurent.NonConst (ι (a i))) :
    ∃ A : R₀[X], A.Monic ∧ A ∣ derivative (monicCentred d a) ∧
      (∀ l j, l ≠ j → W A (monicCentred d a) l j ≠ 0) ∧
      ∃ (x : Fin r → ℂˣ) (q : ℕ), 0 < q ∧ ∀ l,
        ι (W A (monicCentred d a) (q * (l + 1)) (q * l)) ∈ MvLaurent.maxIdeal x ^ (l + 1) := by
  obtain ⟨A, B, n, m, N, hAm, -, hfg, hnm, hBN, hiff⟩ :=
    exists_infiniteOrbitFactor_monicCentred hd a
  set f := monicCentred d a
  refine ⟨A, hAm, ⟨C (d : R₀) * B, by rw [hfg]; ring⟩, fun l j hlj => ?_, ?_⟩
  · refine W_ne_zero hAm f ((algebraMap (FractionRing R₀) (AlgebraicClosure (FractionRing R₀))).comp
      (algebraMap R₀ (FractionRing R₀))) l j fun c hc heq => ?_
    have h := (hiff c).1 (by rw [aeval_eq_eval_map_algebraicClosure]; exact hc)
    exact h.2 ((hasFiniteOrbit_iff_algebraicClosure f c).2 (finite_orbit_of_iterate_eq _ hlj heq))
  · obtain ⟨x, c₀, q, hq, hroot, hcrit, hper⟩ :=
      exists_superAttracting_root hSA ι hd a hnc hnm rfl hBN hfg
    exact ⟨x, q, hq, fun l => map_W_mem_maxIdeal_pow hAm f ι x hq hroot hcrit hper l⟩

end IngramMello
