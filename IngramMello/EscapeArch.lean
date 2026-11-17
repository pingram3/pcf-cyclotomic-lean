import IngramMello.Escape
import IngramMello.Resultants

/-!
# Escape and coefficient bounds over `ℂ` (Proposition 3 of the paper, archimedean part)

* `exists_ingram_local_arch`: `κ ‖c i‖ ^ d ≤ ‖Φ_c (c j)‖` for some `j` (Ingram's Lemma 8,
  archimedean, via the same Nullstellensatz certificate).
* `norm_eval_ge`: if `‖z‖ ≥ 2 d B` then `‖f z‖ ≥ 2 ‖z‖` (escape).
* `exists_arch_bound` (Proposition 3 over `ℂ`): a bound `M = M(d)` on the coefficients and on all
  differences of critical iterates of every PCF monic centred polynomial over `ℂ`.
-/

namespace IngramMello

open Polynomial

section CritEnum

/-- Over `ℂ`, a monic polynomial of degree `n` is `critProd u` for some `u : Fin n → ℂ`. -/
theorem exists_eq_critProd {g : ℂ[X]} (hg : g.Monic) {n : ℕ} (hn : g.natDegree = n) :
    ∃ u : Fin n → ℂ, g = critProd u := by
  classical
  have hcard : Multiset.card g.roots = n := by rw [IsAlgClosed.card_roots_eq_natDegree, hn]
  set L := g.roots.toList with hL
  have hlen : L.length = n := by rw [hL, Multiset.length_toList, hcard]
  refine ⟨fun i => L.get (Fin.cast hlen.symm i), ?_⟩
  have hofn : List.ofFn (fun i : Fin n => L.get (Fin.cast hlen.symm i)) = L := by
    apply List.ext_get (by simp [hlen])
    intro m h₁ h₂
    simp
  have hprod : (g.roots.map fun a => X - C a).prod = g := by
    have := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := g) IsAlgClosed.card_roots_eq_natDegree
    rwa [hg.leadingCoeff, C_1, one_mul] at this
  unfold critProd
  rw [← List.prod_ofFn]
  have hmap : List.ofFn (fun i : Fin n => X - C (L.get (Fin.cast hlen.symm i)))
      = L.map (fun a => X - C a) := by
    calc List.ofFn (fun i : Fin n => X - C (L.get (Fin.cast hlen.symm i)))
        = (List.ofFn fun i : Fin n => L.get (Fin.cast hlen.symm i)).map (fun a => X - C a) :=
          by rw [List.map_ofFn]; rfl
      _ = L.map (fun a => X - C a) := by rw [hofn]
  rw [hmap, ← Multiset.prod_coe, ← Multiset.map_coe, hL, Multiset.coe_toList, hprod]

end CritEnum

section ArchLocal

/-- **Ingram's Lemma 8, archimedean local part.** -/
theorem exists_ingram_local_arch (d : ℕ) (hd : 2 ≤ d) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (c : Fin (d - 1) → ℂ) (i : Fin (d - 1)),
      ∃ j, κ * ‖c i‖ ^ d ≤ ‖(Phi d c).eval (c j)‖ := by
  classical
  obtain ⟨e, Fc, he, hFc⟩ := exists_certificate d hd
  set A : ℝ := ∑ i, ∑ j, ∑ m ∈ (Fc i j).support, ‖algebraMap ℚ ℂ ((Fc i j).coeff m)‖ with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨1 / (1 + A), by positivity, ?_⟩
  intro c i
  have hFbound : ∀ i j (x : Fin (d - 1) → ℂ), (∀ k, ‖x k‖ ≤ 1) →
      ‖MvPolynomial.aeval x (Fc i j)‖
        ≤ ∑ m ∈ (Fc i j).support, ‖algebraMap ℚ ℂ ((Fc i j).coeff m)‖ := by
    intro i j x hx
    rw [MvPolynomial.aeval_eq_eval₂Hom, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul]
    calc _ ≤ ‖algebraMap ℚ ℂ ((Fc i j).coeff m)‖ * 1 := by
          gcongr
          rw [norm_prod]
          exact Finset.prod_le_one₀ (fun k _ => norm_nonneg _)
            (fun k _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hx k))
      _ = _ := mul_one _
  by_cases hci : c i = 0
  · exact ⟨i, by rw [hci, norm_zero, zero_pow (by omega), mul_zero]; exact norm_nonneg _⟩
  have hne : (Finset.univ : Finset (Fin (d - 1))).Nonempty := ⟨i, Finset.mem_univ i⟩
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun k => ‖c k‖) hne
  have hci₀ : c i₀ ≠ 0 := by
    intro h0
    apply hci
    have := hi₀ i (Finset.mem_univ i)
    rw [h0, norm_zero] at this
    exact norm_eq_zero.mp (le_antisymm this (norm_nonneg _))
  have hci₀' : 0 < ‖c i₀‖ := norm_pos_iff.mpr hci₀
  set x : Fin (d - 1) → ℂ := fun k => c k * (c i₀)⁻¹ with hx
  have hcx : ∀ k, c k = c i₀ * x k := fun k => by rw [hx]; simp only; field_simp
  have hx1 : ∀ k, ‖x k‖ ≤ 1 := fun k => by
    rw [hx]; simp only
    rw [norm_mul, norm_inv, mul_inv_le_iff₀ hci₀', one_mul]
    exact hi₀ k (Finset.mem_univ k)
  have hxi₀ : x i₀ = 1 := by rw [hx]; simp only; exact mul_inv_cancel₀ hci₀
  have hcert : (1 : ℂ) = ∑ j, MvPolynomial.aeval x (Fc i₀ j) * (Phi d x).eval (x j) := by
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
  have hlt : ∀ j, ‖(Phi d x).eval (x j)‖ < 1 / (1 + A) := by
    intro j
    have h1 := hcon j
    rw [hhom j, norm_mul, norm_pow] at h1
    have h2 : 1 / (1 + A) * ‖c i‖ ^ d ≤ 1 / (1 + A) * ‖c i₀‖ ^ d := by
      gcongr
      exact hi₀ i (Finset.mem_univ i)
    have h3 := lt_of_lt_of_le h1 h2
    have hpos : 0 < ‖c i₀‖ ^ d := pow_pos hci₀' d
    rw [mul_comm (1 / (1 + A))] at h3
    exact lt_of_mul_lt_mul_left h3 hpos.le
  have hsum : ‖∑ j, MvPolynomial.aeval x (Fc i₀ j) * (Phi d x).eval (x j)‖ < 1 := by
    calc ‖∑ j, MvPolynomial.aeval x (Fc i₀ j) * (Phi d x).eval (x j)‖
        ≤ ∑ j, ‖MvPolynomial.aeval x (Fc i₀ j)‖ * ‖(Phi d x).eval (x j)‖ := by
          refine (norm_sum_le _ _).trans ?_
          simp only [norm_mul, le_refl]
      _ ≤ ∑ j, (∑ m ∈ (Fc i₀ j).support, ‖algebraMap ℚ ℂ ((Fc i₀ j).coeff m)‖)
            * (1 / (1 + A)) :=
          Finset.sum_le_sum fun j _ => mul_le_mul (hFbound i₀ j x hx1) (hlt j).le
            (norm_nonneg _) (by positivity)
      _ = (∑ j, ∑ m ∈ (Fc i₀ j).support, ‖algebraMap ℚ ℂ ((Fc i₀ j).coeff m)‖)
            * (1 / (1 + A)) := by rw [Finset.sum_mul]
      _ ≤ A * (1 / (1 + A)) := by
          gcongr
          exact Finset.single_le_sum
            (f := fun i => ∑ j, ∑ m ∈ (Fc i j).support, ‖algebraMap ℚ ℂ ((Fc i j).coeff m)‖)
            (fun i _ => by positivity) (Finset.mem_univ i₀)
      _ < 1 := by rw [mul_one_div, div_lt_one (by positivity)]; linarith
  rw [← hcert, norm_one] at hsum
  exact lt_irrefl _ hsum

end ArchLocal

section EscapeArch

/-- **Escape lemma over `ℂ`.** -/
theorem norm_eval_ge {f : ℂ[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {B : ℝ} (hB : 1 ≤ B)
    (hcoef : ∀ k < f.natDegree, ‖f.coeff k‖ ≤ B) {z : ℂ}
    (hz : 2 * f.natDegree * B ≤ ‖z‖) : 2 * ‖z‖ ≤ ‖f.eval z‖ := by
  set n := f.natDegree with hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hd
  have hz4 : 4 ≤ ‖z‖ := by nlinarith
  have hz1 : 1 ≤ ‖z‖ := by linarith
  have hS : ‖∑ k ∈ Finset.range n, f.coeff k * z ^ k‖ ≤ n * B * ‖z‖ ^ (n - 1) := by
    calc _ ≤ ∑ k ∈ Finset.range n, ‖f.coeff k * z ^ k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.range n, B * ‖z‖ ^ (n - 1) := Finset.sum_le_sum fun k hk => by
          rw [norm_mul, norm_pow]
          have hk' := Finset.mem_range.mp hk
          exact mul_le_mul (hcoef k hk') (pow_le_pow_right₀ hz1 (by omega)) (by positivity)
            (by linarith)
      _ = n * B * ‖z‖ ^ (n - 1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hzn : ‖z‖ ^ n = ‖z‖ ^ (n - 1) * ‖z‖ := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega)]
  have hfz : f.eval z = (∑ k ∈ Finset.range n, f.coeff k * z ^ k) + z ^ n := by
    rw [eval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_mul]
  have h1 : ‖z‖ ^ n - ‖∑ k ∈ Finset.range n, f.coeff k * z ^ k‖ ≤ ‖f.eval z‖ := by
    rw [hfz, ← norm_pow]
    have := norm_sub_le ((∑ k ∈ Finset.range n, f.coeff k * z ^ k) + z ^ n)
      (∑ k ∈ Finset.range n, f.coeff k * z ^ k)
    rw [add_sub_cancel_left] at this
    linarith
  have h2 : ‖z‖ ^ (n - 1) * (‖z‖ / 2) ≤ ‖f.eval z‖ := by
    have hnB : (n : ℝ) * B ≤ ‖z‖ / 2 := by linarith
    calc ‖z‖ ^ (n - 1) * (‖z‖ / 2) ≤ ‖z‖ ^ (n - 1) * (‖z‖ - n * B) := by
          gcongr; linarith
      _ = ‖z‖ ^ n - n * B * ‖z‖ ^ (n - 1) := by rw [hzn]; ring
      _ ≤ ‖f.eval z‖ := by linarith [h1, hS]
  have h3 : 2 * ‖z‖ ≤ ‖z‖ ^ (n - 1) * (‖z‖ / 2) := by
    have : ‖z‖ ≤ ‖z‖ ^ (n - 1) := by
      calc ‖z‖ = ‖z‖ ^ 1 := (pow_one _).symm
        _ ≤ ‖z‖ ^ (n - 1) := pow_le_pow_right₀ hz1 (by omega)
    nlinarith
  linarith

theorem norm_iterate_of_escape {f : ℂ[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {B : ℝ}
    (hB : 1 ≤ B) (hcoef : ∀ k < f.natDegree, ‖f.coeff k‖ ≤ B) {z : ℂ}
    (hz : 2 * f.natDegree * B ≤ ‖z‖) :
    ∀ m, 2 * f.natDegree * B ≤ ‖(fun w => f.eval w)^[m] z‖ ∧
      ‖(fun w => f.eval w)^[m] z‖ < ‖(fun w => f.eval w)^[m + 1] z‖ := by
  have hn2 : (2 : ℝ) ≤ f.natDegree := by exact_mod_cast hd
  intro m
  induction m with
  | zero =>
    refine ⟨hz, ?_⟩
    show ‖z‖ < ‖f.eval z‖
    have := norm_eval_ge hf hd hB hcoef hz
    nlinarith
  | succ m ih =>
    have hz' : 2 * f.natDegree * B ≤ ‖(fun w => f.eval w)^[m + 1] z‖ := ih.1.trans ih.2.le
    refine ⟨hz', ?_⟩
    rw [Function.iterate_succ_apply' _ (m + 1)]
    have := norm_eval_ge hf hd hB hcoef hz'
    nlinarith

theorem not_hasFiniteOrbit_of_escape_arch {f : ℂ[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree)
    {B : ℝ} (hB : 1 ≤ B) (hcoef : ∀ k < f.natDegree, ‖f.coeff k‖ ≤ B) {z : ℂ}
    (hz : 2 * f.natDegree * B ≤ ‖z‖) : ¬ HasFiniteOrbit f z := by
  unfold HasFiniteOrbit
  have hinj : Function.Injective fun n : ℕ => (fun w => aeval w f)^[n] z := by
    have hsm : StrictMono fun n : ℕ => ‖(fun w => f.eval w)^[n] z‖ :=
      strictMono_nat_of_lt_succ fun n => (norm_iterate_of_escape hf hd hB hcoef hz n).2
    intro n m hnm
    apply hsm.injective
    simp only [coe_aeval_eq_eval] at hnm
    simp only [hnm]
  exact Set.infinite_range_of_injective hinj

theorem norm_iterate_lt_of_hasFiniteOrbit {f : ℂ[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree)
    {B : ℝ} (hB : 1 ≤ B) (hcoef : ∀ k < f.natDegree, ‖f.coeff k‖ ≤ B) {c : ℂ}
    (hc : HasFiniteOrbit f c) (n : ℕ) :
    ‖(fun w => f.eval w)^[n] c‖ < 2 * f.natDegree * B := by
  by_contra h
  push Not at h
  apply not_hasFiniteOrbit_of_escape_arch hf hd hB hcoef h
  unfold HasFiniteOrbit at hc ⊢
  refine hc.subset ?_
  rintro _ ⟨m, rfl⟩
  refine ⟨m + n, ?_⟩
  simp only [coe_aeval_eq_eval, Function.iterate_add_apply]

theorem norm_coeff_critProd_le {R : ℝ} (hR : 1 ≤ R) :
    ∀ {n : ℕ} (u : Fin n → ℂ), (∀ i, ‖u i‖ ≤ R) →
      ∀ k, ‖(critProd u).coeff k‖ ≤ (2 * R) ^ n := by
  intro n
  induction n with
  | zero =>
    intro u _ k
    unfold critProd
    simp only [Finset.univ_eq_empty, Finset.prod_empty, pow_zero, coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    intro u hu k
    have hsplit : critProd u = (X - C (u 0)) * critProd (fun i : Fin n => u i.succ) := by
      unfold critProd
      rw [Fin.prod_univ_succ]
    have hih := ih (fun i : Fin n => u i.succ) (fun i => hu i.succ)
    have hpos : 0 ≤ (2 * R) ^ n := by positivity
    rw [hsplit, sub_mul, coeff_sub, coeff_C_mul, pow_succ]
    refine (norm_sub_le _ _).trans ?_
    have hX : ‖(X * critProd (fun i : Fin n => u i.succ)).coeff k‖ ≤ (2 * R) ^ n := by
      rcases k with _ | k
      · rw [coeff_X_mul_zero, norm_zero]; exact hpos
      · rw [coeff_X_mul]; exact hih k
    have hC : ‖u 0 * (critProd (fun i : Fin n => u i.succ)).coeff k‖ ≤ R * (2 * R) ^ n := by
      rw [norm_mul]; exact mul_le_mul (hu 0) (hih k) (norm_nonneg _) (by linarith)
    nlinarith

end EscapeArch

section ArchMain

/-- **Proposition 3, archimedean case.** A bound `M = M(d)` on the coefficients and on
all differences of critical iterates of every PCF monic centred polynomial over `ℂ`. -/
theorem exists_arch_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ M : ℝ, ∀ a : Fin (d - 1) → ℂ, IsPCF (monicCentred d a) →
      (∀ k, ‖a k‖ ≤ M) ∧
      ∀ c : ℂ, (derivative (monicCentred d a)).IsRoot c → ∀ n m : ℕ,
        ‖(fun z => (monicCentred d a).eval z)^[n] c -
          (fun z => (monicCentred d a).eval z)^[m] c‖ ≤ M := by
  classical
  obtain ⟨κ, hκ, hloc⟩ := exists_ingram_local_arch d hd
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  set R₁ : ℝ := max 1 (d * 2 ^ d / κ) with hR₁
  have hR₁1 : 1 ≤ R₁ := le_max_left _ _
  set C₁ : ℝ := 2 * R₁ with hC₁
  have hC₁1 : 1 ≤ C₁ := by linarith
  set C₂ : ℝ := d * (2 * C₁) ^ (d - 1) with hC₂
  have hC₂0 : 0 ≤ C₂ := by positivity
  set Ma : ℝ := R₁ + R₁ ^ d + d * C₂ * R₁ ^ d + C₂ with hMa
  set B : ℝ := max 1 Ma with hB
  have hB1 : 1 ≤ B := le_max_left _ _
  have hMaB : Ma ≤ B := le_max_right _ _
  refine ⟨4 * d * B, ?_⟩
  intro a hpcf
  set f := monicCentred d a with hf
  have hfm : f.Monic := monicCentred_monic hd a
  have hfdeg : f.natDegree = d := monicCentred_natDegree hd a
  obtain ⟨g₀, hg₀m, hg₀deg, hfg₀⟩ := exists_derivative_monicCentred hd a
  obtain ⟨c, rfl⟩ := exists_eq_critProd hg₀m hg₀deg
  have hc : derivative f = C (d : ℂ) * critProd c := hfg₀
  obtain ⟨p, hp⟩ : ∃ p : ℂ, f.eval p = p := by
    have hdeg : 0 < (f - X).degree := by
      rw [degree_sub_eq_left_of_degree_lt]
      · rw [degree_eq_natDegree hfm.ne_zero, hfdeg]; exact_mod_cast (show 0 < d by omega)
      · rw [degree_X, degree_eq_natDegree hfm.ne_zero, hfdeg]
        exact_mod_cast (show 1 < d by omega)
    obtain ⟨p, hp⟩ := Complex.exists_root hdeg
    exact ⟨p, by rw [IsRoot, eval_sub, eval_X, sub_eq_zero] at hp; exact hp⟩
  have horb : ∀ i, HasFiniteOrbit f (c i) := fun i =>
    hpcf (c i) (by
      rw [hc, IsRoot, eval_mul, (critProd_isRoot_iff c (c i)).mpr ⟨i, rfl⟩, mul_zero])
  obtain ⟨hgPhi, hgm, hgdeg⟩ := conjFixed_monicCentred hd a c p hc hp
  obtain ⟨hg0, hgcoef⟩ := conjFixed_coeff hd a c p hc hp
  set g := conjFixed f p with hg
  set c' : Fin (d - 1) → ℂ := fun i => c i - p with hc'
  have horb' : ∀ j, HasFiniteOrbit g (c' j) := fun j =>
    hasFiniteOrbit_conjFixed f p (c j) (horb j)
  /- Step 1: `‖c'_i‖ ≤ R₁`. -/
  have hstep1 : ∀ i, ‖c' i‖ ≤ R₁ := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := hcon
    have hne : (Finset.univ : Finset (Fin (d - 1))).Nonempty := ⟨i, Finset.mem_univ i⟩
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun k => ‖c' k‖) hne
    set R := ‖c' i₀‖ with hR
    have hRR₁ : R₁ < R := lt_of_lt_of_le hi (hi₀ i (Finset.mem_univ i))
    have hR1 : 1 ≤ R := hR₁1.trans hRR₁.le
    have hRκ : d * 2 ^ d < κ * R := by
      have : d * 2 ^ d / κ < R := lt_of_le_of_lt (le_max_right _ _) hRR₁
      rw [div_lt_iff₀ hκ] at this
      linarith
    obtain ⟨j, hj⟩ := hloc c' i₀
    have hgj : d * κ * R ^ d ≤ ‖g.eval (c' j)‖ := by
      rw [hgPhi, eval_mul, eval_C, norm_mul, Complex.norm_natCast, mul_assoc]
      exact mul_le_mul_of_nonneg_left hj (by positivity)
    set Bg : ℝ := d * (2 * R) ^ (d - 1) with hBg
    have hBg1 : 1 ≤ Bg := by
      have : (1 : ℝ) ≤ (2 * R) ^ (d - 1) := one_le_pow₀ (by linarith)
      nlinarith
    have hcoefg : ∀ k < g.natDegree, ‖g.coeff k‖ ≤ Bg := by
      intro k hk
      rw [hgdeg] at hk
      rcases k with _ | k
      · rw [hg0, norm_zero]; exact zero_le_one.trans hBg1
      · have h1 := hgcoef k
        have hprod : ‖(critProd c').coeff k‖ ≤ (2 * R) ^ (d - 1) :=
          norm_coeff_critProd_le hR1 c' (fun i => hi₀ i (Finset.mem_univ i)) k
        have hk1 : (1 : ℝ) ≤ ‖(k : ℂ) + 1‖ := by
          rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
          exact_mod_cast Nat.succ_pos k
        have h2 : ‖g.coeff (k + 1)‖ * ‖(k : ℂ) + 1‖ ≤ Bg := by
          rw [← norm_mul, h1, norm_mul, Complex.norm_natCast, hBg]
          exact mul_le_mul_of_nonneg_left hprod (by positivity)
        calc ‖g.coeff (k + 1)‖ = ‖g.coeff (k + 1)‖ * 1 := (mul_one _).symm
          _ ≤ ‖g.coeff (k + 1)‖ * ‖(k : ℂ) + 1‖ := by gcongr
          _ ≤ Bg := h2
    have hthr : 2 * (g.natDegree : ℝ) * Bg ≤ ‖g.eval (c' j)‖ := by
      refine le_trans ?_ hgj
      rw [hgdeg, hBg]
      have hRd : R ^ d = R * R ^ (d - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      have h2d : (2 : ℝ) ^ d = 2 * 2 ^ (d - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      rw [hRd, mul_pow]
      have hRpos : 0 ≤ R ^ (d - 1) := by positivity
      have := mul_le_mul_of_nonneg_right hRκ.le hRpos
      rw [h2d] at this
      nlinarith
    have := norm_iterate_lt_of_hasFiniteOrbit hgm (by rw [hgdeg]; exact hd) hBg1 hcoefg
      (horb' j) 1
    simp only [Function.iterate_one] at this
    exact absurd hthr (not_le.mpr this)
  /- Step 2: `‖p‖ ≤ R₁`, `‖c_i‖ ≤ C₁`. -/
  have hsum := sum_crit_eq_zero hd a c hc
  have hp' : ((d - 1 : ℕ) : ℂ) * p = -∑ i, c' i := by
    simp only [hc', Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hpR : ‖p‖ ≤ R₁ := by
    have hd1 : (0 : ℝ) < ((d - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < d - 1 by omega)
    have h1 : ((d - 1 : ℕ) : ℝ) * ‖p‖ ≤ ((d - 1 : ℕ) : ℝ) * R₁ := by
      calc ((d - 1 : ℕ) : ℝ) * ‖p‖ = ‖((d - 1 : ℕ) : ℂ) * p‖ := by
            rw [norm_mul, Complex.norm_natCast]
        _ = ‖∑ i, c' i‖ := by rw [hp', norm_neg]
        _ ≤ ∑ i : Fin (d - 1), ‖c' i‖ := norm_sum_le _ _
        _ ≤ ∑ i : Fin (d - 1), R₁ := Finset.sum_le_sum fun i _ => hstep1 i
        _ = ((d - 1 : ℕ) : ℝ) * R₁ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact le_of_mul_le_mul_left h1 hd1
  have hcC₁ : ∀ i, ‖c i‖ ≤ C₁ := by
    intro i
    have : c i = c' i + p := by simp [hc']
    rw [this]
    calc ‖c' i + p‖ ≤ ‖c' i‖ + ‖p‖ := norm_add_le _ _
      _ ≤ R₁ + R₁ := add_le_add (hstep1 i) hpR
      _ = C₁ := by rw [hC₁]; ring
  /- Step 3: the coefficients. -/
  have hak : ∀ k : Fin (d - 1), 1 ≤ (k : ℕ) → ‖a k‖ ≤ C₂ := by
    intro k hk
    obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨k - 1, by omega⟩
    have hder := coeff_derivative f j
    rw [hc, coeff_C_mul, ← hj, monicCentred_coeff_of_lt a k.isLt, Fin.eta] at hder
    have hprod : ‖(critProd c).coeff j‖ ≤ (2 * C₁) ^ (d - 1) :=
      norm_coeff_critProd_le hC₁1 c hcC₁ j
    have hk1 : (1 : ℝ) ≤ ‖(j : ℂ) + 1‖ := by
      rw [show ((j : ℂ) + 1) = ((j + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
      exact_mod_cast Nat.succ_pos j
    have h2 : ‖a k‖ * ‖(j : ℂ) + 1‖ ≤ C₂ := by
      rw [← norm_mul, ← hder, norm_mul, Complex.norm_natCast, hC₂]
      exact mul_le_mul_of_nonneg_left hprod (by positivity)
    calc ‖a k‖ = ‖a k‖ * 1 := (mul_one _).symm
      _ ≤ ‖a k‖ * ‖(j : ℂ) + 1‖ := by gcongr
      _ ≤ C₂ := h2
  have haM : ∀ k, ‖a k‖ ≤ Ma := by
    intro k
    by_cases hk : (k : ℕ) = 0
    · have ha0 : a k = p - p ^ d - ∑ i ∈ Finset.univ.erase k, a i * p ^ (i : ℕ) := by
        have h := hp
        rw [hf, monicCentred_eval, ← Finset.add_sum_erase _ _ (Finset.mem_univ k), hk, pow_zero,
          mul_one] at h
        linear_combination h
      rw [ha0]
      have hsum : ‖∑ i ∈ Finset.univ.erase k, a i * p ^ (i : ℕ)‖ ≤ d * C₂ * R₁ ^ d := by
        calc _ ≤ ∑ i ∈ Finset.univ.erase k, ‖a i * p ^ (i : ℕ)‖ := norm_sum_le _ _
          _ ≤ ∑ i ∈ Finset.univ.erase k, C₂ * R₁ ^ d := Finset.sum_le_sum fun i hi => by
              have hi1 : 1 ≤ (i : ℕ) := by
                rcases Finset.mem_erase.mp hi with ⟨hne, -⟩
                by_contra h
                exact hne (Fin.ext (by rw [hk]; omega))
              rw [norm_mul, norm_pow]
              exact mul_le_mul (hak i hi1)
                ((pow_le_pow_left₀ (norm_nonneg _) hpR _).trans
                  (pow_le_pow_right₀ hR₁1 (by have := i.isLt; omega)))
                (by positivity) hC₂0
          _ = (Finset.univ.erase k).card * (C₂ * R₁ ^ d) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ d * (C₂ * R₁ ^ d) := by
              gcongr
              calc (Finset.univ.erase k).card
                  ≤ (Finset.univ : Finset (Fin (d - 1))).card :=
                    Finset.card_le_card (Finset.erase_subset _ _)
                _ ≤ d := by rw [Finset.card_univ, Fintype.card_fin]; exact Nat.sub_le d 1
          _ = d * C₂ * R₁ ^ d := by ring
      calc ‖p - p ^ d - ∑ i ∈ Finset.univ.erase k, a i * p ^ (i : ℕ)‖
          ≤ ‖p - p ^ d‖ + ‖∑ i ∈ Finset.univ.erase k, a i * p ^ (i : ℕ)‖ := norm_sub_le _ _
        _ ≤ (‖p‖ + ‖p ^ d‖) + d * C₂ * R₁ ^ d := add_le_add (norm_sub_le _ _) hsum
        _ ≤ (R₁ + R₁ ^ d) + d * C₂ * R₁ ^ d := by
            gcongr
            rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg _) hpR _
        _ ≤ Ma := by rw [hMa]; linarith
    · have := hak k (by omega)
      rw [hMa]
      have : 0 ≤ R₁ + R₁ ^ d + d * C₂ * R₁ ^ d := by positivity
      linarith
  refine ⟨fun k => (haM k).trans (hMaB.trans ?_), ?_⟩
  · nlinarith
  · intro c₀ hc₀ n m
    have hcoef : ∀ k < f.natDegree, ‖f.coeff k‖ ≤ B := by
      intro k hk
      rw [hfdeg] at hk
      by_cases hk' : k < d - 1
      · rw [hf, monicCentred_coeff_of_lt a hk']; exact (haM _).trans hMaB
      · rw [hf, monicCentred_coeff_eq_zero a (by omega) hk, norm_zero]; linarith
    have horb₀ : HasFiniteOrbit f c₀ := hpcf c₀ hc₀
    have h1 := norm_iterate_lt_of_hasFiniteOrbit hfm (by rw [hfdeg]; exact hd) hB1 hcoef horb₀ n
    have h2 := norm_iterate_lt_of_hasFiniteOrbit hfm (by rw [hfdeg]; exact hd) hB1 hcoef horb₀ m
    rw [hfdeg] at h1 h2
    calc _ ≤ ‖(fun z => f.eval z)^[n] c₀‖ + ‖(fun z => f.eval z)^[m] c₀‖ := norm_sub_le _ _
      _ ≤ 4 * d * B := by linarith

end ArchMain

end IngramMello
