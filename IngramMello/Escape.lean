import IngramMello.IngramForms
import IngramMello.Statements

/-!
# Escape and local coefficient bounds (Proposition 3 of the paper, non-archimedean part)

Over any field `F` with a valuation `v : F → Γ₀`:

* `val_eval_eq_pow` (escape): if `f` is monic of degree `d ≥ 2` with `v (coeff) ≤ B`,
  `1 ≤ B`, and `B < v z`, then `v (f z) = v z ^ d`.
* `val_iterate_le_of_hasFiniteOrbit`: a point with finite forward orbit has all iterates
  of valuation `≤ B`.
* `exists_local_coeff_bound` (Ingram's Lemma 8 and Proposition 3(i), ultrametric case): there is
  `N = N(d) ≥ 1` such that for every field `F` of characteristic zero with a valuation, every
  monic centred `f` whose critical points and one fixed point lie in `F` and whose critical
  points have finite orbit satisfies `v (N * a_k) ≤ 1` for all coefficients, and
  `v (N * (fⁿ(c) - fᵐ(c))) ≤ 1` for all critical points `c ∈ F`.
-/

namespace IngramMello

open Polynomial

/-! ### Basic facts about `monicCentred` -/

section MonicCentred

variable {R : Type*} [CommRing R]

theorem monicCentred_eq (d : ℕ) (a : Fin (d - 1) → R) :
    monicCentred d a = X ^ d + ∑ i : Fin (d - 1), C (a i) * X ^ (i : ℕ) := rfl

theorem natDegree_monicCentred_sum_le (d : ℕ) (a : Fin (d - 1) → R) :
    (∑ i : Fin (d - 1), C (a i) * X ^ (i : ℕ)).natDegree ≤ d - 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem monicCentred_monic [Nontrivial R] {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R) :
    (monicCentred d a).Monic := by
  rw [monicCentred_eq]
  apply monic_X_pow_add
  have := natDegree_monicCentred_sum_le d a
  rw [← degree_X_pow (R := R) d]
  exact degree_lt_degree (by rw [natDegree_X_pow]; omega)

theorem monicCentred_natDegree [Nontrivial R] {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R) :
    (monicCentred d a).natDegree = d := by
  rw [monicCentred_eq, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  have := natDegree_monicCentred_sum_le d a
  omega

theorem monicCentred_coeff_of_lt {d : ℕ} (a : Fin (d - 1) → R) {k : ℕ} (hk : k < d - 1) :
    (monicCentred d a).coeff k = a ⟨k, hk⟩ := by
  rw [monicCentred_eq, coeff_add, coeff_X_pow, ite_eq_right (by omega), zero_add, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single ⟨k, hk⟩]
  · simp
  · intro b _ hb
    rw [ite_eq_right]
    intro h
    apply hb
    exact Fin.ext h.symm
  · simp

theorem monicCentred_coeff_eq_zero {d : ℕ} (a : Fin (d - 1) → R) {k : ℕ} (hk : d - 1 ≤ k)
    (hk' : k < d) : (monicCentred d a).coeff k = 0 := by
  rw [monicCentred_eq, coeff_add, coeff_X_pow, ite_eq_right (by omega), zero_add, finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul_X_pow, ite_eq_right]
  have := i.isLt
  omega

theorem monicCentred_eval {d : ℕ} (a : Fin (d - 1) → R) (z : R) :
    (monicCentred d a).eval z = z ^ d + ∑ i : Fin (d - 1), a i * z ^ (i : ℕ) := by
  simp [monicCentred_eq, eval_finsetSum]


theorem critProd_isRoot_iff {F : Type*} [Field F] {n : ℕ} (u : Fin n → F) (r : F) :
    (critProd u).IsRoot r ↔ ∃ i, u i = r := by
  unfold critProd
  rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, eval_sub, eval_X, eval_C, sub_eq_zero]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

/-- The critical points of a monic centred polynomial sum to zero. -/
theorem sum_crit_eq_zero {F : Type*} [Field F] [CharZero F] {d : ℕ} (hd : 2 ≤ d)
    (a : Fin (d - 1) → F) (c : Fin (d - 1) → F)
    (hc : derivative (monicCentred d a) = C (d : F) * critProd c) : ∑ i, c i = 0 := by
  have h1 : (derivative (monicCentred d a)).coeff (d - 2) = 0 := by
    rw [coeff_derivative, monicCentred_coeff_eq_zero a (by omega) (by omega), zero_mul]
  rw [hc, coeff_C_mul] at h1
  have h2 : (critProd c).coeff (d - 2) = -∑ i, c i := by
    unfold critProd
    have := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (d - 1))) c
      (by simp; omega)
    rw [Finset.card_univ, Fintype.card_fin, show d - 1 - 1 = d - 2 by omega] at this
    exact this
  rw [h2, mul_neg, neg_eq_zero, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr (by omega))
  · exact h1

end MonicCentred

/-! ### Bookkeeping: `v (M * x) ≤ 1` -/

section Bdd

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

theorem vbdd_of_dvd {M M' : ℕ} (h : M ∣ M') {x : F} (hx : v ((M : F) * x) ≤ 1) :
    v ((M' : F) * x) ≤ 1 := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm (M : F), mul_assoc, Valuation.map_mul]
  calc v (t : F) * v ((M : F) * x) ≤ 1 * 1 := mul_le_mul' (val_natCast_le_one v t) hx
    _ = 1 := mul_one 1

theorem vbdd_add {M : ℕ} {x y : F} (hx : v ((M : F) * x) ≤ 1) (hy : v ((M : F) * y) ≤ 1) :
    v ((M : F) * (x + y)) ≤ 1 := by
  rw [mul_add]; exact v.map_add_le hx hy

theorem vbdd_neg {M : ℕ} {x : F} (hx : v ((M : F) * x) ≤ 1) : v ((M : F) * (-x)) ≤ 1 := by
  rw [mul_neg, Valuation.map_neg]; exact hx

theorem vbdd_sub {M : ℕ} {x y : F} (hx : v ((M : F) * x) ≤ 1) (hy : v ((M : F) * y) ≤ 1) :
    v ((M : F) * (x - y)) ≤ 1 := by
  rw [sub_eq_add_neg]; exact vbdd_add v hx (vbdd_neg v hy)

theorem vbdd_mul {M M' : ℕ} {x y : F} (hx : v ((M : F) * x) ≤ 1) (hy : v ((M' : F) * y) ≤ 1) :
    v (((M * M' : ℕ) : F) * (x * y)) ≤ 1 := by
  rw [Nat.cast_mul, show (M : F) * M' * (x * y) = ((M : F) * x) * ((M' : F) * y) by ring,
    Valuation.map_mul]
  calc v ((M : F) * x) * v ((M' : F) * y) ≤ 1 * 1 := mul_le_mul' hx hy
    _ = 1 := mul_one 1

theorem vbdd_pow {M : ℕ} {x : F} (hx : v ((M : F) * x) ≤ 1) (n : ℕ) :
    v (((M ^ n : ℕ) : F) * x ^ n) ≤ 1 := by
  rw [Nat.cast_pow, ← mul_pow, Valuation.map_pow]
  exact pow_le_one' hx n

theorem vbdd_sum {M : ℕ} {ι : Type*} (s : Finset ι) {x : ι → F}
    (hx : ∀ i ∈ s, v ((M : F) * x i) ≤ 1) : v ((M : F) * ∑ i ∈ s, x i) ≤ 1 := by
  rw [Finset.mul_sum]; exact v.map_sum_le hx

theorem vbdd_natCast {M : ℕ} (n : ℕ) : v ((M : F) * (n : F)) ≤ 1 := by
  rw [← Nat.cast_mul]; exact val_natCast_le_one v _

theorem vbdd_one_of_le {M : ℕ} {x : F} (hx : v x ≤ 1) : v ((M : F) * x) ≤ 1 := by
  rw [Valuation.map_mul]
  calc v (M : F) * v x ≤ 1 * 1 := mul_le_mul' (val_natCast_le_one v M) hx
    _ = 1 := mul_one 1

/-- `v (M * x) ≤ 1` means `v x ≤ (v M)⁻¹`. -/
theorem le_inv_of_vbdd [CharZero F] {M : ℕ} (hM : 0 < M) {x : F} (hx : v ((M : F) * x) ≤ 1) :
    v x ≤ (v (M : F))⁻¹ := by
  have hM0 : v (M : F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr hM.ne'
  rw [Valuation.map_mul] at hx
  calc v x = (v (M : F))⁻¹ * (v (M : F) * v x) := by rw [inv_mul_cancel_left₀ hM0]
    _ ≤ (v (M : F))⁻¹ * 1 := mul_le_mul_right hx _
    _ = (v (M : F))⁻¹ := mul_one _

theorem vbdd_of_le_inv [CharZero F] {M : ℕ} (hM : 0 < M) {x : F} (hx : v x ≤ (v (M : F))⁻¹) :
    v ((M : F) * x) ≤ 1 := by
  have hM0 : v (M : F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr hM.ne'
  rw [Valuation.map_mul]
  calc v (M : F) * v x ≤ v (M : F) * (v (M : F))⁻¹ := mul_le_mul_right hx _
    _ = 1 := mul_inv_cancel₀ hM0

theorem one_le_inv_val_natCast [CharZero F] {M : ℕ} (hM : 0 < M) : 1 ≤ (v (M : F))⁻¹ := by
  have hM0 : v (M : F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr hM.ne'
  rw [one_le_inv₀ (zero_lt_iff.mpr hM0)]
  exact val_natCast_le_one v M

end Bdd

/-! ### Coefficients of products of monic linear factors -/

section ProdCoeff

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

theorem val_coeff_critProd_le {R : Γ₀} (hR : 1 ≤ R) :
    ∀ {n : ℕ} (u : Fin n → F), (∀ i, v (u i) ≤ R) → ∀ k, v ((critProd u).coeff k) ≤ R ^ n := by
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
    rw [hsplit, sub_mul, coeff_sub, coeff_C_mul]
    have hRn : R ^ n ≤ R ^ (n + 1) := pow_le_pow_right' hR (Nat.le_succ n)
    refine v.map_sub_le ?_ ?_
    · rcases k with _ | k
      · rw [coeff_X_mul_zero, Valuation.map_zero]; exact zero_le
      · rw [coeff_X_mul]; exact (hih k).trans hRn
    · rw [Valuation.map_mul, pow_succ']
      exact mul_le_mul' (hu 0) (hih k)

end ProdCoeff

/-! ### Escape -/

section Escape

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

/-- **Escape lemma.** -/
theorem val_eval_eq_pow {f : F[X]} (hf : f.Monic) (_hd : 2 ≤ f.natDegree) {B : Γ₀} (hB : 1 ≤ B)
    (hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ B) {z : F} (hz : B < v z) :
    v (f.eval z) = v z ^ f.natDegree := by
  have h1 : 1 < v z := lt_of_le_of_lt hB hz
  have hz0 : v z ≠ 0 := (zero_lt_one.trans h1).ne'
  rw [eval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_mul]
  rw [Valuation.map_add_eq_of_lt_right, Valuation.map_pow]
  rw [Valuation.map_pow]
  refine v.map_sum_lt (pow_ne_zero _ hz0) fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Valuation.map_mul, Valuation.map_pow]
  calc v (f.coeff k) * v z ^ k ≤ B * v z ^ k := mul_le_mul_left (hcoef k hk) _
    _ < v z * v z ^ k := mul_lt_mul_of_pos_right hz (pow_pos (zero_lt_one.trans h1) k)
    _ = v z ^ (k + 1) := (pow_succ' _ _).symm
    _ ≤ v z ^ f.natDegree := pow_le_pow_right' h1.le hk

theorem val_iterate_of_escape {f : F[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {B : Γ₀}
    (hB : 1 ≤ B) (hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ B) {z : F} (hz : B < v z) :
    ∀ n, B < v ((fun w => f.eval w)^[n] z) ∧
      v ((fun w => f.eval w)^[n] z) < v ((fun w => f.eval w)^[n + 1] z) := by
  intro n
  induction n with
  | zero =>
    refine ⟨hz, ?_⟩
    show v z < v (f.eval z)
    rw [val_eval_eq_pow v hf hd hB hcoef hz]
    have h1 : 1 < v z := lt_of_le_of_lt hB hz
    calc v z = v z * 1 := (mul_one _).symm
      _ < v z * v z ^ (f.natDegree - 1) :=
          mul_lt_mul_of_pos_left (one_lt_pow' h1 (by omega)) (zero_lt_one.trans h1)
      _ = v z ^ f.natDegree := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  | succ n ih =>
    have hz' : B < v ((fun w => f.eval w)^[n + 1] z) := ih.1.trans ih.2
    refine ⟨hz', ?_⟩
    rw [Function.iterate_succ_apply' _ (n + 1), val_eval_eq_pow v hf hd hB hcoef hz']
    have h1 : 1 < v ((fun w => f.eval w)^[n + 1] z) := lt_of_le_of_lt hB hz'
    calc v ((fun w => f.eval w)^[n + 1] z) = v ((fun w => f.eval w)^[n + 1] z) * 1 :=
          (mul_one _).symm
      _ < v ((fun w => f.eval w)^[n + 1] z) * v ((fun w => f.eval w)^[n + 1] z) ^ (f.natDegree - 1) :=
          mul_lt_mul_of_pos_left (one_lt_pow' h1 (by omega)) (zero_lt_one.trans h1)
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]

theorem not_hasFiniteOrbit_of_escape {f : F[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {B : Γ₀}
    (hB : 1 ≤ B) (hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ B) {z : F} (hz : B < v z) :
    ¬ HasFiniteOrbit f z := by
  unfold HasFiniteOrbit
  have hinj : Function.Injective fun n : ℕ => (fun w => aeval w f)^[n] z := by
    have hsm : StrictMono fun n : ℕ => v ((fun w => f.eval w)^[n] z) :=
      strictMono_nat_of_lt_succ fun n => (val_iterate_of_escape v hf hd hB hcoef hz n).2
    intro n m hnm
    apply hsm.injective
    simp only [coe_aeval_eq_eval] at hnm
    simp only [hnm]
  exact Set.infinite_range_of_injective hinj

/-- Iterates of a point with finite orbit stay in the ball of radius `B`. -/
theorem val_iterate_le_of_hasFiniteOrbit {f : F[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree)
    {B : Γ₀} (hB : 1 ≤ B) (hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ B) {c : F}
    (hc : HasFiniteOrbit f c) (n : ℕ) : v ((fun w => f.eval w)^[n] c) ≤ B := by
  by_contra h
  push Not at h
  apply not_hasFiniteOrbit_of_escape v hf hd hB hcoef h
  unfold HasFiniteOrbit at hc ⊢
  refine hc.subset ?_
  rintro _ ⟨m, rfl⟩
  refine ⟨m + n, ?_⟩
  simp only [coe_aeval_eq_eval, Function.iterate_add_apply]

/-- `z` **escapes** under `f` at `v`: some iterate leaves a ball of radius `B ≥ 1` containing
all coefficients of `f`. By `val_iterate_of_escape` the valuations of the iterates then grow
strictly and the orbit is infinite. The negation says that every admissible `B` bounds the whole
orbit. -/
def Escapes (f : F[X]) (z : F) : Prop :=
  ∃ B : Γ₀, 1 ≤ B ∧ (∀ k < f.natDegree, v (f.coeff k) ≤ B) ∧
    ∃ n : ℕ, B < v ((fun w => f.eval w)^[n] z)

theorem not_escapes_of_hasFiniteOrbit {f : F[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {c : F}
    (hc : HasFiniteOrbit f c) : ¬ Escapes v f c := by
  rintro ⟨B, hB, hcoef, n, hlt⟩
  exact absurd hlt (not_lt.mpr (val_iterate_le_of_hasFiniteOrbit v hf hd hB hcoef hc n))

theorem not_hasFiniteOrbit_of_escapes {f : F[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {c : F}
    (hc : Escapes v f c) : ¬ HasFiniteOrbit f c := by
  obtain ⟨B, hB, hcoef, n, hlt⟩ := hc
  intro hfin
  exact absurd hlt (not_lt.mpr (val_iterate_le_of_hasFiniteOrbit v hf hd hB hcoef hfin n))

end Escape


/-! ### Conjugation by a fixed point -/

section Conj

variable {F : Type*} [Field F] [CharZero F]

/-- `g = f (X + p) - p`: conjugation of `f` by the translation `z ↦ z + p`. -/
noncomputable def conjFixed (f : F[X]) (p : F) : F[X] := f.comp (X + C p) - C p

theorem conjFixed_eval (f : F[X]) (p w : F) : (conjFixed f p).eval w = f.eval (w + p) - p := by
  simp [conjFixed, eval_comp]

theorem conjFixed_iterate (f : F[X]) (p z : F) (n : ℕ) :
    (fun w => (conjFixed f p).eval w)^[n] (z - p) = (fun w => f.eval w)^[n] z - p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, conjFixed_eval,
      sub_add_cancel]

theorem hasFiniteOrbit_conjFixed (f : F[X]) (p z : F) (hz : HasFiniteOrbit f z) :
    HasFiniteOrbit (conjFixed f p) (z - p) := by
  unfold HasFiniteOrbit at hz ⊢
  refine (hz.image (fun w => w - p)).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨(fun w => aeval w f)^[n] z, ⟨n, rfl⟩, ?_⟩
  simp only [coe_aeval_eq_eval]
  exact (conjFixed_iterate f p z n).symm

/-- For `f` monic centred with `f' = d ∏ (X - c i)` and `f p = p`, the conjugate
`g = f (X + p) - p` equals `d · Φ_{c - p}`, and is monic of degree `d`. -/
theorem conjFixed_monicCentred {d : ℕ} (hd : 2 ≤ d) (a c : Fin (d - 1) → F) (p : F)
    (hc : derivative (monicCentred d a) = C (d : F) * critProd c)
    (hp : (monicCentred d a).eval p = p) :
    conjFixed (monicCentred d a) p = C (d : F) * Phi d (fun i => c i - p) ∧
      (conjFixed (monicCentred d a) p).Monic ∧
      (conjFixed (monicCentred d a) p).natDegree = d := by
  set f := monicCentred d a with hf
  have hfm : f.Monic := monicCentred_monic hd a
  have hfdeg : f.natDegree = d := monicCentred_natDegree hd a
  set g := conjFixed f p with hg
  have hg' : derivative g = C (d : F) * critProd (fun i => c i - p) := by
    rw [hg, conjFixed, derivative_sub, derivative_C, sub_zero, derivative_comp, hc,
      derivative_add, derivative_X, derivative_C, add_zero, one_mul, mul_comp, C_comp]
    congr 1
    unfold critProd
    rw [prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sub_comp, X_comp, C_comp, C_sub]; ring
  have hg0 : g.eval 0 = 0 := by rw [hg, conjFixed_eval, zero_add, hp, sub_self]
  have hcompm : (f.comp (X + C p)).Monic :=
    hfm.comp (monic_X_add_C p) (by rw [natDegree_X_add_C]; exact one_ne_zero)
  have hcompdeg : (f.comp (X + C p)).natDegree = d := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one, hfdeg]
  refine ⟨?_, ?_, ?_⟩
  · have hder : derivative (g - C (d : F) * Phi d (fun i => c i - p)) = 0 := by
      rw [derivative_sub, hg', derivative_mul, derivative_C, zero_mul, zero_add,
        derivative_Phi d (by omega), sub_self]
    have h0 : (g - C (d : F) * Phi d (fun i => c i - p)).eval 0 = 0 := by
      simp [hg0, eval_zero_Phi]
    have := eq_C_of_derivative_eq_zero hder
    rw [coeff_zero_eq_eval_zero, h0, C_0] at this
    exact sub_eq_zero.mp this
  · rw [hg, conjFixed]
    refine Monic.sub_of_left hcompm ?_
    refine degree_C_le.trans_lt ?_
    rw [degree_eq_natDegree hcompm.ne_zero, hcompdeg]
    exact_mod_cast (show 0 < d by omega)
  · rw [hg, conjFixed, natDegree_sub_C, hcompdeg]

/-- The coefficients of the conjugate are controlled by `c - p` through its derivative:
`(k+1) g_{k+1} = d · coeff_k ∏ (X - (c i - p))` and `g_0 = 0`. -/
theorem conjFixed_coeff {d : ℕ} (hd : 2 ≤ d) (a c : Fin (d - 1) → F) (p : F)
    (hc : derivative (monicCentred d a) = C (d : F) * critProd c)
    (hp : (monicCentred d a).eval p = p) :
    (conjFixed (monicCentred d a) p).coeff 0 = 0 ∧
      ∀ k, (conjFixed (monicCentred d a) p).coeff (k + 1) * ((k : F) + 1)
        = (d : F) * (critProd (fun i => c i - p)).coeff k := by
  obtain ⟨hgPhi, -, -⟩ := conjFixed_monicCentred hd a c p hc hp
  refine ⟨?_, ?_⟩
  · rw [coeff_zero_eq_eval_zero, conjFixed_eval, zero_add, hp, sub_self]
  · intro k
    have hder := coeff_derivative (conjFixed (monicCentred d a) p) k
    rw [hgPhi, derivative_mul, derivative_C, zero_mul, zero_add, derivative_Phi d (by omega),
      coeff_C_mul] at hder
    rw [hgPhi]
    exact hder.symm

end Conj

/-! ### The local coefficient bound -/

section Main

universe u w

/-- **Local coefficient bound, non-escaping form** (Ingram's Lemma 8 and Proposition 3(i),
ultrametric case). There is `N = N(d) ≥ 1` such that over every valued field of characteristic
zero, every monic centred polynomial whose critical points `c i` (with `f' = d ∏ (X - c i)`)
and some fixed point `p` lie in the field, and none of whose critical points escapes
(`Escapes`), has `v (N * a_k) ≤ 1` for every coefficient. Finite critical orbits are a special
case (`exists_local_coeff_bound`); over function fields the critical orbits are infinite and
only non-escape is available. -/
theorem exists_local_coeff_bound_of_not_escapes (d : ℕ) (hd : 2 ≤ d) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (F : Type u) [Field F] [CharZero F] (Γ₀ : Type w) [LinearOrderedCommGroupWithZero Γ₀]
        (v : Valuation F Γ₀) (a : Fin (d - 1) → F) (c : Fin (d - 1) → F) (p : F),
        derivative (monicCentred d a) = C (d : F) * critProd c →
        (monicCentred d a).eval p = p →
        (∀ i, ¬ Escapes v (monicCentred d a) (c i)) →
        ∀ k, v ((N : F) * a k) ≤ 1 := by
  classical
  obtain ⟨N₀, hN₀, hloc⟩ := exists_ingram_local.{u, w} d hd
  set N₂ : ℕ := d * N₀ * d.factorial with hN₂
  set M₁ : ℕ := (d - 1) * N₂ with hM₁
  have hN₂pos : 0 < N₂ := by positivity
  have hM₁pos : 0 < M₁ := Nat.mul_pos (by omega) hN₂pos
  refine ⟨d.factorial * M₁ ^ (2 * d), by positivity, ?_⟩
  intro F _ _ Γ₀ _ v a c p hc hp hnesc
  set f := monicCentred d a with hf
  have hfm : f.Monic := monicCentred_monic hd a
  have hfdeg : f.natDegree = d := monicCentred_natDegree hd a
  /- Step 0: conjugate by the fixed point: `g = f (X + p) - p = d Φ_{c'}`. -/
  set c' : Fin (d - 1) → F := fun i => c i - p with hc'
  set g : F[X] := f.comp (X + C p) - C p with hg
  have hg' : derivative g = C (d : F) * critProd c' := by
    rw [hg, derivative_sub, derivative_C, sub_zero, derivative_comp, hc, derivative_add,
      derivative_X, derivative_C, add_zero, one_mul, mul_comp, C_comp]
    congr 1
    unfold critProd
    rw [prod_comp]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [sub_comp, X_comp, C_comp, hc']
    simp only
    rw [C_sub]; ring
  have hg0 : g.eval 0 = 0 := by
    rw [hg, eval_sub, eval_comp, eval_add, eval_X, eval_C, zero_add, hp, sub_self]
  have hgPhi : g = C (d : F) * Phi d c' := by
    have hder : derivative (g - C (d : F) * Phi d c') = 0 := by
      rw [derivative_sub, hg', derivative_mul, derivative_C, zero_mul, zero_add,
        derivative_Phi d (by omega), sub_self]
    have h0 : (g - C (d : F) * Phi d c').eval 0 = 0 := by simp [hg0, eval_zero_Phi]
    have := eq_C_of_derivative_eq_zero hder
    rw [coeff_zero_eq_eval_zero, h0, C_0] at this
    exact sub_eq_zero.mp this
  have hcompm : (f.comp (X + C p)).Monic :=
    hfm.comp (monic_X_add_C p) (by rw [natDegree_X_add_C]; exact one_ne_zero)
  have hcompdeg : (f.comp (X + C p)).natDegree = d := by
    rw [natDegree_comp, natDegree_X_add_C, mul_one, hfdeg]
  have hgm : g.Monic := by
    rw [hg]
    refine Monic.sub_of_left hcompm ?_
    refine degree_C_le.trans_lt ?_
    rw [degree_eq_natDegree hcompm.ne_zero, hcompdeg]
    exact_mod_cast (show 0 < d by omega)
  have hgdeg : g.natDegree = d := by rw [hg, natDegree_sub_C, hcompdeg]
  have hgiter : ∀ j n, (fun w => g.eval w)^[n] (c' j) = (fun w => f.eval w)^[n] (c j) - p := by
    intro j n
    induction n with
    | zero => simp [hc']
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hg, eval_sub, eval_comp,
        eval_add, eval_X, eval_C, sub_add_cancel]
  /- Step 1: `v (N₂ c'_i) ≤ 1`. -/
  have hstep1 : ∀ i, v ((N₂ : F) * c' i) ≤ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨i, hi⟩ := hcon
    have hne : (Finset.univ : Finset (Fin (d - 1))).Nonempty := ⟨i, Finset.mem_univ i⟩
    obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image Finset.univ (fun k => v (c' k)) hne
    set R := v (c' i₀) with hR
    have hR1 : 1 < v (N₂ : F) * R := by
      calc 1 < v ((N₂ : F) * c' i) := hi
        _ = v (N₂ : F) * v (c' i) := Valuation.map_mul _ _ _
        _ ≤ v (N₂ : F) * R := mul_le_mul_right (hi₀ i (Finset.mem_univ i)) _
    have hRgt : 1 < R := by
      by_contra h
      push Not at h
      have : v (N₂ : F) * R ≤ 1 * 1 := mul_le_mul' (val_natCast_le_one v N₂) h
      rw [one_mul] at this
      exact absurd hR1 (not_lt.mpr this)
    have hR0 : 0 < R := zero_lt_one.trans hRgt
    obtain ⟨j, hj⟩ := hloc F Γ₀ v c' i₀
    have hgj : v (d : F) * v (N₀ : F) * R ^ d ≤ v (g.eval (c' j)) := by
      rw [hgPhi, eval_mul, eval_C, Valuation.map_mul, mul_assoc]
      exact mul_le_mul_right hj _
    have hfact0 : v (d.factorial : F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr (Nat.factorial_pos d).ne'
    set Bg : Γ₀ := (v (d.factorial : F))⁻¹ * R ^ (d - 1) with hBg
    have hBg1 : 1 ≤ Bg := by
      calc (1 : Γ₀) = 1 * 1 := (mul_one 1).symm
        _ ≤ Bg := mul_le_mul' (one_le_inv_val_natCast v (Nat.factorial_pos d))
            (one_le_pow_of_one_le' hRgt.le _)
    have hcoefg : ∀ k < g.natDegree, v (g.coeff k) ≤ Bg := by
      intro k hk
      rw [hgdeg] at hk
      rcases k with _ | k
      · rw [coeff_zero_eq_eval_zero, hg0, Valuation.map_zero]; exact zero_le
      · have hder := coeff_derivative g k
        rw [hg', coeff_C_mul] at hder
        have hprod : v ((critProd c').coeff k) ≤ R ^ (d - 1) :=
          val_coeff_critProd_le v hRgt.le c' (fun i => hi₀ i (Finset.mem_univ i)) k
        have hk1 : v ((k : F) + 1) ≠ 0 := by
          rw [Valuation.ne_zero_iff]; exact Nat.cast_add_one_ne_zero k
        have h1 : v (g.coeff (k + 1)) * v ((k : F) + 1) ≤ R ^ (d - 1) := by
          rw [← Valuation.map_mul, ← hder, Valuation.map_mul]
          calc v (d : F) * v ((critProd c').coeff k) ≤ 1 * R ^ (d - 1) :=
                mul_le_mul' (val_natCast_le_one v d) hprod
            _ = R ^ (d - 1) := one_mul _
        have h2 : v (g.coeff (k + 1)) ≤ (v ((k : F) + 1))⁻¹ * R ^ (d - 1) := by
          calc v (g.coeff (k + 1))
              = (v ((k : F) + 1))⁻¹ * (v (g.coeff (k + 1)) * v ((k : F) + 1)) := by
                rw [mul_comm (v (g.coeff _)), inv_mul_cancel_left₀ hk1]
            _ ≤ (v ((k : F) + 1))⁻¹ * R ^ (d - 1) := mul_le_mul_right h1 _
        have h3 : (v ((k : F) + 1))⁻¹ ≤ (v (d.factorial : F))⁻¹ := by
          rw [inv_le_inv₀ (zero_lt_iff.mpr hk1) (zero_lt_iff.mpr hfact0)]
          obtain ⟨t, ht⟩ := Nat.dvd_factorial (Nat.succ_pos k) (by omega : k + 1 ≤ d)
          rw [ht, Nat.cast_mul, Valuation.map_mul, Nat.cast_succ]
          calc v ((k : F) + 1) * v (t : F) ≤ v ((k : F) + 1) * 1 :=
                mul_le_mul_right (val_natCast_le_one v t) _
            _ = v ((k : F) + 1) := mul_one _
        exact h2.trans (mul_le_mul_left h3 _)
    have hBglt : Bg < v (g.eval (c' j)) := by
      refine lt_of_lt_of_le ?_ hgj
      have hRd : R ^ d = R * R ^ (d - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel (by omega)]
      have hsplit : v (d : F) * v (N₀ : F) * R ^ d
          = (v (d : F) * v (N₀ : F) * R) * R ^ (d - 1) := by
        rw [hRd]; ac_rfl
      rw [hBg, hsplit]
      refine mul_lt_mul_of_pos_right ?_ (pow_pos hR0 _)
      have hN₂v : v (d.factorial : F) * (v (d : F) * v (N₀ : F) * R) = v (N₂ : F) * R := by
        rw [hN₂, Nat.cast_mul, Nat.cast_mul, Valuation.map_mul, Valuation.map_mul]
        ac_rfl
      calc (v (d.factorial : F))⁻¹ = (v (d.factorial : F))⁻¹ * 1 := (mul_one _).symm
        _ < (v (d.factorial : F))⁻¹ * (v (d.factorial : F) * (v (d : F) * v (N₀ : F) * R)) := by
            rw [hN₂v]
            exact mul_lt_mul_of_pos_left hR1 (inv_pos.mpr (zero_lt_iff.mpr hfact0))
        _ = v (d : F) * v (N₀ : F) * R := inv_mul_cancel_left₀ hfact0 _
    /- `g(c'_j)` escapes under `g`, so `c_j` escapes under `f`. -/
    have hgd : 2 ≤ g.natDegree := by rw [hgdeg]; exact hd
    set γ := v (g.eval (c' j)) with hγ
    have hRBg : R ≤ Bg := by
      calc R ≤ R ^ (d - 1) := le_self_pow hRgt.le (by omega)
        _ = 1 * R ^ (d - 1) := (one_mul _).symm
        _ ≤ Bg := mul_le_mul' (one_le_inv_val_natCast v (Nat.factorial_pos d)) le_rfl
    have hRγ : R ≤ γ := hRBg.trans hBglt.le
    have hiter : ∀ m, v ((fun w => g.eval w)^[m] (g.eval (c' j))) = γ ^ (d ^ m) := by
      intro m
      induction m with
      | zero => simp [hγ]
      | succ m ih =>
        rw [Function.iterate_succ_apply', val_eval_eq_pow v hgm hgd hBg1 hcoefg
          (val_iterate_of_escape v hgm hgd hBg1 hcoefg hBglt m).1, ih, hgdeg, ← pow_mul,
          pow_succ]
    have hd1 : v ((d - 1 : ℕ) : F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr (by omega)
    set R' : Γ₀ := (v ((d - 1 : ℕ) : F))⁻¹ * R with hR'
    have hRR' : R ≤ R' := by
      calc R = 1 * R := (one_mul R).symm
        _ ≤ R' := mul_le_mul' (one_le_inv_val_natCast v (by omega)) le_rfl
    have hR'1 : 1 ≤ R' := hRgt.le.trans hRR'
    have hsum0 := sum_crit_eq_zero hd a c hc
    have hp0 : ((d - 1 : ℕ) : F) * p = -∑ i, c' i := by
      simp only [hc', Finset.sum_sub_distrib, hsum0, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring
    have hpR' : v p ≤ R' := by
      have h1 : v ((d - 1 : ℕ) : F) * v p ≤ R := by
        rw [← Valuation.map_mul, hp0, Valuation.map_neg]
        exact v.map_sum_le fun i _ => hi₀ i (Finset.mem_univ i)
      calc v p = (v ((d - 1 : ℕ) : F))⁻¹ * (v ((d - 1 : ℕ) : F) * v p) := by
            rw [inv_mul_cancel_left₀ hd1]
        _ ≤ R' := mul_le_mul' le_rfl h1
    have hcR' : ∀ i, v (c i) ≤ R' := by
      intro i
      have : c i = c' i + p := by simp [hc']
      rw [this]
      exact (v.map_add _ _).trans (max_le ((hi₀ i (Finset.mem_univ i)).trans hRR') hpR')
    have hcoef_crit' : ∀ k, v ((critProd c).coeff k) ≤ R' ^ (d - 1) :=
      val_coeff_critProd_le v hR'1 c hcR'
    set Bf : Γ₀ := (v (d.factorial : F))⁻¹ * R' ^ (2 * d) with hBf
    have hfact1 : 1 ≤ (v (d.factorial : F))⁻¹ := one_le_inv_val_natCast v (Nat.factorial_pos d)
    have hBf1 : 1 ≤ Bf := by
      calc (1 : Γ₀) = 1 * 1 := (mul_one 1).symm
        _ ≤ Bf := mul_le_mul' hfact1 (one_le_pow_of_one_le' hR'1 _)
    have hR'Bf : R' ≤ Bf := by
      calc R' = 1 * R' ^ 1 := by rw [one_mul, pow_one]
        _ ≤ Bf := mul_le_mul' hfact1 (pow_le_pow_right' hR'1 (by omega))
    have hak' : ∀ k : Fin (d - 1), 1 ≤ (k : ℕ) →
        v (a k) ≤ (v (d.factorial : F))⁻¹ * R' ^ (d - 1) := by
      intro k hk
      obtain ⟨j', hj'⟩ : ∃ j', (k : ℕ) = j' + 1 := ⟨k - 1, by omega⟩
      have hder := coeff_derivative f j'
      rw [hc, coeff_C_mul, ← hj', monicCentred_coeff_of_lt a k.isLt, Fin.eta] at hder
      have hk1 : v ((j' : F) + 1) ≠ 0 := by
        rw [Valuation.ne_zero_iff]; exact Nat.cast_add_one_ne_zero j'
      have h1 : v (a k) * v ((j' : F) + 1) ≤ R' ^ (d - 1) := by
        rw [← Valuation.map_mul, ← hder, Valuation.map_mul]
        calc v (d : F) * v ((critProd c).coeff j') ≤ 1 * R' ^ (d - 1) :=
              mul_le_mul' (val_natCast_le_one v d) (hcoef_crit' j')
          _ = R' ^ (d - 1) := one_mul _
      have h2 : v (a k) ≤ (v ((j' : F) + 1))⁻¹ * R' ^ (d - 1) := by
        calc v (a k) = (v ((j' : F) + 1))⁻¹ * (v (a k) * v ((j' : F) + 1)) := by
              rw [mul_comm (v (a k)), inv_mul_cancel_left₀ hk1]
          _ ≤ (v ((j' : F) + 1))⁻¹ * R' ^ (d - 1) := mul_le_mul' le_rfl h1
      have h3 : (v ((j' : F) + 1))⁻¹ ≤ (v (d.factorial : F))⁻¹ := by
        rw [inv_le_inv₀ (zero_lt_iff.mpr hk1) (zero_lt_iff.mpr hfact0)]
        obtain ⟨t, ht⟩ := Nat.dvd_factorial (Nat.succ_pos j') (by omega : j' + 1 ≤ d)
        rw [ht, Nat.cast_mul, Valuation.map_mul, Nat.cast_succ]
        calc v ((j' : F) + 1) * v (t : F) ≤ v ((j' : F) + 1) * 1 :=
              mul_le_mul' le_rfl (val_natCast_le_one v t)
          _ = v ((j' : F) + 1) := mul_one _
      exact h2.trans (mul_le_mul' h3 le_rfl)
    have hcoefF : ∀ k < f.natDegree, v (f.coeff k) ≤ Bf := by
      intro k hk
      rw [hfdeg] at hk
      by_cases hk' : k < d - 1
      · rw [hf, monicCentred_coeff_of_lt a hk']
        by_cases hk0 : k = 0
        · subst hk0
          have ha0 : a ⟨0, hk'⟩ = p - p ^ d -
              ∑ i ∈ Finset.univ.erase (⟨0, hk'⟩ : Fin (d - 1)), a i * p ^ (i : ℕ) := by
            have h := hp
            rw [monicCentred_eval,
              ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hk'⟩ : Fin (d - 1)))] at h
            simp only [pow_zero, mul_one] at h
            linear_combination h
          rw [ha0]
          have hpBf : v p ≤ Bf := hpR'.trans hR'Bf
          have hpdBf : v (p ^ d) ≤ Bf := by
            rw [Valuation.map_pow]
            calc v p ^ d ≤ R' ^ d := pow_le_pow_left' hpR' d
              _ = 1 * R' ^ d := (one_mul _).symm
              _ ≤ Bf := mul_le_mul' hfact1 (pow_le_pow_right' hR'1 (by omega))
          refine (v.map_sub _ _).trans
            (max_le ((v.map_sub _ _).trans (max_le hpBf hpdBf)) ?_)
          refine v.map_sum_le fun i hi => ?_
          have hi1 : 1 ≤ (i : ℕ) := by
            rcases Finset.mem_erase.mp hi with ⟨hne', -⟩
            by_contra h
            exact hne' (Fin.ext (show (i : ℕ) = 0 by omega))
          rw [Valuation.map_mul, Valuation.map_pow]
          calc v (a i) * v p ^ (i : ℕ)
              ≤ ((v (d.factorial : F))⁻¹ * R' ^ (d - 1)) * R' ^ (d - 1) :=
                mul_le_mul' (hak' i hi1) ((pow_le_pow_left' hpR' _).trans
                  (pow_le_pow_right' hR'1 (by have := i.isLt; omega)))
            _ = (v (d.factorial : F))⁻¹ * R' ^ (d - 1 + (d - 1)) := by
                rw [mul_assoc, ← pow_add]
            _ ≤ Bf := mul_le_mul' le_rfl (pow_le_pow_right' hR'1 (by omega))
        · calc v (a ⟨k, hk'⟩) ≤ (v (d.factorial : F))⁻¹ * R' ^ (d - 1) :=
                hak' ⟨k, hk'⟩ (by simp only; omega)
            _ ≤ Bf := mul_le_mul' le_rfl (pow_le_pow_right' hR'1 (by omega))
      · rw [hf, monicCentred_coeff_eq_zero a (by omega) hk, Valuation.map_zero]
        exact zero_le
    /- `Bf ≤ R ^ (4d+1)`, using `1 < v N₂ * R` and `d! (d-1)^{2d} ∣ N₂^{2d+1}`. -/
    have hN₂0 : v (N₂ : F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr hN₂pos.ne'
    have hinvN₂ : (v (N₂ : F))⁻¹ ≤ R := by
      calc (v (N₂ : F))⁻¹ = (v (N₂ : F))⁻¹ * 1 := (mul_one _).symm
        _ ≤ (v (N₂ : F))⁻¹ * (v (N₂ : F) * R) := mul_le_mul' le_rfl hR1.le
        _ = R := inv_mul_cancel_left₀ hN₂0 _
    have hdvdN : d.factorial * (d - 1) ^ (2 * d) ∣ N₂ ^ (2 * d + 1) := by
      rw [pow_succ, mul_comm d.factorial]
      refine mul_dvd_mul ?_ (Dvd.intro_left _ rfl)
      refine pow_dvd_pow_of_dvd ?_ _
      exact (Nat.dvd_factorial (by omega) (by omega)).trans (Dvd.intro_left _ rfl)
    have hconst : (v (d.factorial : F))⁻¹ * ((v ((d - 1 : ℕ) : F))⁻¹) ^ (2 * d)
        ≤ R ^ (2 * d + 1) := by
      obtain ⟨t, ht⟩ := hdvdN
      have h1 : v ((N₂ ^ (2 * d + 1) : ℕ) : F)
          ≤ v ((d.factorial * (d - 1) ^ (2 * d) : ℕ) : F) := by
        rw [ht, Nat.cast_mul, Valuation.map_mul]
        calc _ ≤ v ((d.factorial * (d - 1) ^ (2 * d) : ℕ) : F) * 1 :=
              mul_le_mul' le_rfl (val_natCast_le_one v t)
          _ = _ := mul_one _
      have h2 : v ((d.factorial * (d - 1) ^ (2 * d) : ℕ) : F) ≠ 0 := by
        rw [Valuation.ne_zero_iff]
        exact Nat.cast_ne_zero.mpr
          (Nat.mul_pos (Nat.factorial_pos d) (pow_pos (by omega) _)).ne'
      have h3 : v ((N₂ ^ (2 * d + 1) : ℕ) : F) ≠ 0 := by
        rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr (pow_pos hN₂pos _).ne'
      calc (v (d.factorial : F))⁻¹ * ((v ((d - 1 : ℕ) : F))⁻¹) ^ (2 * d)
          = (v ((d.factorial * (d - 1) ^ (2 * d) : ℕ) : F))⁻¹ := by
            rw [Nat.cast_mul, Nat.cast_pow, Valuation.map_mul, Valuation.map_pow, mul_inv,
              inv_pow]
        _ ≤ (v ((N₂ ^ (2 * d + 1) : ℕ) : F))⁻¹ := by
            rw [inv_le_inv₀ (zero_lt_iff.mpr h2) (zero_lt_iff.mpr h3)]; exact h1
        _ = ((v (N₂ : F))⁻¹) ^ (2 * d + 1) := by
            rw [Nat.cast_pow, Valuation.map_pow, inv_pow]
        _ ≤ R ^ (2 * d + 1) := pow_le_pow_left' hinvN₂ _
    have hBfR : Bf ≤ R ^ (4 * d + 1) := by
      calc Bf = ((v (d.factorial : F))⁻¹ * ((v ((d - 1 : ℕ) : F))⁻¹) ^ (2 * d)) * R ^ (2 * d) := by
            rw [hBf, hR', mul_pow, mul_assoc]
        _ ≤ R ^ (2 * d + 1) * R ^ (2 * d) := mul_le_mul' hconst le_rfl
        _ = R ^ (4 * d + 1) := by rw [← pow_add]; congr 1; omega
    set m : ℕ := 4 * d + 1 with hm
    have hpowm : 4 * d + 1 < d ^ m := Nat.lt_pow_self (by omega)
    have hbig : R ^ (4 * d + 1) < v ((fun w => g.eval w)^[m] (g.eval (c' j))) := by
      rw [hiter m]
      calc R ^ (4 * d + 1) < R ^ (d ^ m) := pow_lt_pow_right₀ hRgt hpowm
        _ ≤ γ ^ (d ^ m) := pow_le_pow_left' hRγ _
    have hfn : (fun w => f.eval w)^[m + 1] (c j)
        = (fun w => g.eval w)^[m] (g.eval (c' j)) + p := by
      have := hgiter j (m + 1)
      rw [Function.iterate_succ_apply] at this
      rw [this, sub_add_cancel]
    have hlt : Bf < v ((fun w => f.eval w)^[m + 1] (c j)) := by
      rw [hfn, Valuation.map_add_eq_of_lt_left]
      · exact lt_of_le_of_lt hBfR hbig
      · exact lt_of_le_of_lt (hpR'.trans hR'Bf) (lt_of_le_of_lt hBfR hbig)
    exact hnesc j ⟨Bf, hBf1, hcoefF, m + 1, hlt⟩
  /- Step 2: `v (M₁ p) ≤ 1` and `v (M₁ c_i) ≤ 1`. -/
  have hsum := sum_crit_eq_zero hd a c hc
  have hp' : ((d - 1 : ℕ) : F) * p = -∑ i, c' i := by
    simp only [hc', Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  have hpM : v ((M₁ : F) * p) ≤ 1 := by
    rw [hM₁, Nat.cast_mul, mul_assoc, mul_left_comm, hp', mul_neg, Valuation.map_neg,
      Finset.mul_sum]
    exact v.map_sum_le fun i _ => hstep1 i
  have hcM : ∀ i, v ((M₁ : F) * c i) ≤ 1 := by
    intro i
    have : c i = c' i + p := by simp [hc']
    rw [this]
    exact vbdd_add v (vbdd_of_dvd v (Dvd.intro_left _ rfl) (hstep1 i)) hpM
  /- Step 3: the coefficients. -/
  have hcoef_crit : ∀ k, v ((critProd c).coeff k) ≤ ((v (M₁ : F))⁻¹) ^ (d - 1) :=
    val_coeff_critProd_le v (one_le_inv_val_natCast v hM₁pos) c
      (fun i => le_inv_of_vbdd v hM₁pos (hcM i))
  have hak : ∀ k : Fin (d - 1), 1 ≤ (k : ℕ) →
      v (((d.factorial * M₁ ^ (d - 1) : ℕ) : F) * a k) ≤ 1 := by
    intro k hk
    obtain ⟨j, hj⟩ : ∃ j, (k : ℕ) = j + 1 := ⟨k - 1, by omega⟩
    have hder := coeff_derivative f j
    rw [hc, coeff_C_mul, ← hj, monicCentred_coeff_of_lt a k.isLt, Fin.eta] at hder
    have hjk : ((j : F) + 1) = ((k : ℕ) : F) := by rw [hj]; push_cast; ring
    rw [hjk] at hder
    have h1 : v (((M₁ ^ (d - 1) : ℕ) : F) * (((k : ℕ) : F) * a k)) ≤ 1 := by
      rw [mul_comm ((k : ℕ) : F), ← hder, mul_left_comm, Valuation.map_mul]
      calc v (d : F) * v (((M₁ ^ (d - 1) : ℕ) : F) * (critProd c).coeff j) ≤ 1 * 1 :=
            mul_le_mul' (val_natCast_le_one v d) (vbdd_of_le_inv v (by positivity)
              (by rw [Nat.cast_pow, Valuation.map_pow, ← inv_pow]; exact hcoef_crit j))
        _ = 1 := mul_one 1
    obtain ⟨t, ht⟩ := Nat.dvd_factorial (by omega : 0 < (k : ℕ)) (by omega : (k : ℕ) ≤ d)
    have h2 := vbdd_of_dvd v (Dvd.intro_left t rfl : M₁ ^ (d - 1) ∣ t * M₁ ^ (d - 1)) h1
    have h3 : (((t * M₁ ^ (d - 1) : ℕ) : F) * (((k : ℕ) : F) * a k))
        = ((d.factorial * M₁ ^ (d - 1) : ℕ) : F) * a k := by
      rw [ht]; push_cast; ring
    rwa [h3] at h2
  have hdvd1 : M₁ ∣ d.factorial * M₁ ^ (2 * d) :=
    Dvd.dvd.mul_left (dvd_pow_self M₁ (by omega)) _
  have hdvd2 : M₁ ^ d ∣ d.factorial * M₁ ^ (2 * d) :=
    Dvd.dvd.mul_left (pow_dvd_pow M₁ (by omega)) _
  have hdvd3 : d.factorial * M₁ ^ (d - 1) ∣ d.factorial * M₁ ^ (2 * d) :=
    mul_dvd_mul_left _ (pow_dvd_pow M₁ (by omega))
  have hdvd4 : ∀ i : Fin (d - 1), d.factorial * M₁ ^ (d - 1) * M₁ ^ (i : ℕ)
      ∣ d.factorial * M₁ ^ (2 * d) := by
    intro i
    rw [mul_assoc, ← pow_add]
    exact mul_dvd_mul_left _ (pow_dvd_pow M₁ (by have := i.isLt; omega))
  intro k
  by_cases hk : (k : ℕ) = 0
  · have hk0 : k = ⟨0, by omega⟩ := Fin.ext hk
    have ha0 : a k = p - p ^ d - ∑ i ∈ Finset.univ.erase k, a i * p ^ (i : ℕ) := by
      have h := hp
      rw [monicCentred_eval, ← Finset.add_sum_erase _ _ (Finset.mem_univ k), hk, pow_zero,
        mul_one] at h
      linear_combination h
    rw [ha0]
    refine vbdd_sub v (vbdd_sub v (vbdd_of_dvd v hdvd1 hpM) ?_) ?_
    · have := vbdd_pow v hpM d
      exact vbdd_of_dvd v hdvd2 this
    · refine vbdd_sum v _ fun i hi => ?_
      have hi1 : 1 ≤ (i : ℕ) := by
        rcases Finset.mem_erase.mp hi with ⟨hne, -⟩
        by_contra h
        exact hne (Fin.ext (by rw [hk]; omega))
      have := vbdd_mul v (hak i hi1) (vbdd_pow v hpM (i : ℕ))
      exact vbdd_of_dvd v (hdvd4 i) this
  · exact vbdd_of_dvd v hdvd3 (hak k (by omega))

/-- **Local coefficient bound** (Ingram's Lemma 8 and Proposition 3(i), ultrametric case),
finite-orbit form. -/
theorem exists_local_coeff_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (F : Type u) [Field F] [CharZero F] (Γ₀ : Type w) [LinearOrderedCommGroupWithZero Γ₀]
        (v : Valuation F Γ₀) (a : Fin (d - 1) → F) (c : Fin (d - 1) → F) (p : F),
        derivative (monicCentred d a) = C (d : F) * critProd c →
        (monicCentred d a).eval p = p →
        (∀ i, HasFiniteOrbit (monicCentred d a) (c i)) →
        ∀ k, v ((N : F) * a k) ≤ 1 := by
  obtain ⟨N, hN, h⟩ := exists_local_coeff_bound_of_not_escapes.{u, w} d hd
  refine ⟨N, hN, fun F _ _ Γ₀ _ v a c p hc hp horb => h F Γ₀ v a c p hc hp fun i => ?_⟩
  exact not_escapes_of_hasFiniteOrbit v (monicCentred_monic hd a)
    (by rw [monicCentred_natDegree hd a]; exact hd) (horb i)

/-- **Local form of Proposition 3** (ultrametric case): coefficient bound plus bound
on all differences of iterates of points with finite orbit. -/
theorem exists_local_bound (d : ℕ) (hd : 2 ≤ d) :
    ∃ N : ℕ, 0 < N ∧
      ∀ (F : Type u) [Field F] [CharZero F] (Γ₀ : Type w) [LinearOrderedCommGroupWithZero Γ₀]
        (v : Valuation F Γ₀) (a : Fin (d - 1) → F) (c : Fin (d - 1) → F) (p : F),
        derivative (monicCentred d a) = C (d : F) * critProd c →
        (monicCentred d a).eval p = p →
        (∀ i, HasFiniteOrbit (monicCentred d a) (c i)) →
        (∀ k, v ((N : F) * a k) ≤ 1) ∧
        ∀ z : F, HasFiniteOrbit (monicCentred d a) z → ∀ n m : ℕ,
          v ((N : F) * ((fun w => (monicCentred d a).eval w)^[n] z -
            (fun w => (monicCentred d a).eval w)^[m] z)) ≤ 1 := by
  obtain ⟨N, hN, hbound⟩ := exists_local_coeff_bound.{u, w} d hd
  refine ⟨N, hN, ?_⟩
  intro F _ _ Γ₀ _ v a c p hc hp horb
  have ha := hbound F Γ₀ v a c p hc hp horb
  refine ⟨ha, ?_⟩
  intro z hz n m
  set f := monicCentred d a with hf
  have hfm : f.Monic := monicCentred_monic hd a
  have hfdeg : f.natDegree = d := monicCentred_natDegree hd a
  have hB1 : (1 : Γ₀) ≤ (v (N : F))⁻¹ := one_le_inv_val_natCast v hN
  have hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ (v (N : F))⁻¹ := by
    intro k hk
    rw [hfdeg] at hk
    by_cases hk' : k < d - 1
    · rw [hf, monicCentred_coeff_of_lt a hk']
      exact le_inv_of_vbdd v hN (ha _)
    · rw [hf, monicCentred_coeff_eq_zero a (by omega) hk, Valuation.map_zero]
      exact zero_le
  have h1 := val_iterate_le_of_hasFiniteOrbit v hfm (by rw [hfdeg]; exact hd) hB1 hcoef hz n
  have h2 := val_iterate_le_of_hasFiniteOrbit v hfm (by rw [hfdeg]; exact hd) hB1 hcoef hz m
  exact vbdd_of_le_inv v hN (v.map_sub_le h1 h2)

end Main

end IngramMello
