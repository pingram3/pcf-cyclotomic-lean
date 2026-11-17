import Mathlib
import IngramMello.Escape
import IngramMello.Places

/-!
# Super-attracting parameters: the algebraic core

The valuation-theoretic core of the proof of `SuperAttracting` (Lemma 6 of the paper in the
one-parameter case). Everything here is about a monic polynomial
`f` of degree `d ≥ 2` over a field `E` carrying `ℤᵐ⁰`-valued valuations.

* `val_eval_sub_eval_le`, `val_iterate_sub_iterate_le`: the non-archimedean Lipschitz estimate
  `w(fᵍ(x) − fᵍ(y)) ≤ w(x − y) · (B^d)^g` on the ball of radius `B`.
* `exists_escape_data`: a point escaping at `w` has `w(f^q(c) − c) = γ^{d^{q−n}}`, `γ > 1`, for
  `q ≥ n`.
* `false_of_escapes_of_prod_val_eq_one`: the main lemma. Indices `p : ι` (finite) carry a
  valuation `w p` and a point `z p` that is not periodic for `f`. If some `z p₀` escapes at
  `w p₀` while `∏_p w p (f^q(z p) − z p) = 1` for every `q ≥ 1`, we get a contradiction
  (pigeonhole on the indices, then the Lipschitz estimate makes some `z p` periodic).
-/

namespace IngramMello

open Polynomial

/-! ### Generic valuation lemmas -/

section Generic

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

/-- Some `B ≥ 1` bounds the valuations of the coefficients of `f` below the leading one. -/
theorem exists_coef_bound (f : F[X]) :
    ∃ B : Γ₀, 1 ≤ B ∧ ∀ k < f.natDegree, v (f.coeff k) ≤ B :=
  ⟨1 ⊔ (Finset.range f.natDegree).sup fun k => v (f.coeff k), le_sup_left, fun k hk =>
    le_sup_of_le_right (Finset.le_sup (f := fun k => v (f.coeff k)) (Finset.mem_range.mpr hk))⟩

/-- **Lipschitz estimate (one step).** On the ball of radius `B ≥ 1` containing the
coefficients, `w(f(x) − f(y)) ≤ w(x − y) · B^d`. -/
theorem val_eval_sub_eval_le {f : F[X]} (hf : f.Monic) {B : Γ₀} (hB : 1 ≤ B)
    (hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ B) {x y : F} (hx : v x ≤ B) (hy : v y ≤ B) :
    v (f.eval x - f.eval y) ≤ v (x - y) * B ^ f.natDegree := by
  have hxy : f.eval x - f.eval y = (x - y) * ∑ i ∈ Finset.range (f.natDegree + 1),
      f.coeff i * ∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j) := by
    rw [eval_eq_sum_range, eval_eq_sum_range, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, ← geom_sum₂_mul]; ring
  rw [hxy, Valuation.map_mul]
  refine mul_le_mul' le_rfl (v.map_sum_le fun i hi => ?_)
  rw [Finset.mem_range] at hi
  rw [Valuation.map_mul]
  have hci : v (f.coeff i) ≤ B := by
    rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
    · exact hcoef i h
    · rw [h, hf.coeff_natDegree, Valuation.map_one]; exact hB
  have hsum : v (∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j)) ≤ B ^ (i - 1) := by
    refine v.map_sum_le fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Valuation.map_mul, Valuation.map_pow, Valuation.map_pow]
    calc v x ^ j * v y ^ (i - 1 - j) ≤ B ^ j * B ^ (i - 1 - j) :=
          mul_le_mul' (pow_le_pow_left' hx j) (pow_le_pow_left' hy _)
      _ = B ^ (i - 1) := by rw [← pow_add]; congr 1; omega
  rcases Nat.eq_zero_or_pos i with hi0 | hi0
  · subst hi0
    simp only [Finset.range_zero, Finset.sum_empty, Valuation.map_zero, mul_zero]
    exact zero_le
  · calc v (f.coeff i) * v (∑ j ∈ Finset.range i, x ^ j * y ^ (i - 1 - j))
        ≤ B * B ^ (i - 1) := mul_le_mul' hci hsum
      _ = B ^ i := by rw [← pow_succ']; congr 1; omega
      _ ≤ B ^ f.natDegree := pow_le_pow_right' hB (by omega)

/-- **Lipschitz estimate (iterated).** If the orbits of `x` and `y` stay in the ball of radius
`B`, then `w(fᵍ(x) − fᵍ(y)) ≤ w(x − y) · (B^d)^g`. -/
theorem val_iterate_sub_iterate_le {f : F[X]} (hf : f.Monic) {B : Γ₀} (hB : 1 ≤ B)
    (hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ B) {x y : F}
    (hx : ∀ m, v ((fun z => f.eval z)^[m] x) ≤ B)
    (hy : ∀ m, v ((fun z => f.eval z)^[m] y) ≤ B) (g : ℕ) :
    v ((fun z => f.eval z)^[g] x - (fun z => f.eval z)^[g] y)
      ≤ v (x - y) * (B ^ f.natDegree) ^ g := by
  induction g with
  | zero => simp
  | succ g ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', pow_succ, ← mul_assoc]
    exact (val_eval_sub_eval_le v hf hB hcoef (hx g) (hy g)).trans (mul_le_mul' ih le_rfl)

/-- **Escape data.** If `c` escapes at `v` then for some `n` and `γ > 1`,
`v(f^q(c) − c) = γ^{d^{q−n}}` for all `q ≥ n`. -/
theorem exists_escape_data {f : F[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {c : F}
    (h : Escapes v f c) :
    ∃ (n : ℕ) (γ : Γ₀), 1 < γ ∧ ∀ q, n ≤ q →
      v ((fun z => f.eval z)^[q] c - c) = γ ^ (f.natDegree ^ (q - n)) := by
  obtain ⟨B, hB, hcoef, n, hn⟩ := h
  set F := fun z => f.eval z with hF
  have hesc := val_iterate_of_escape v hf hd hB hcoef hn
  have hγ : B < v (F^[n + 1] c) := by
    have := (hesc 1).1
    rwa [← Function.iterate_add_apply, add_comm] at this
  refine ⟨n + 1, v (F^[n + 1] c), lt_of_le_of_lt hB hγ, fun q hq => ?_⟩
  have hpow : ∀ m, v (F^[m + (n + 1)] c) = v (F^[n + 1] c) ^ (f.natDegree ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hB' : B < v (F^[m + (n + 1)] c) := by
        have := (hesc (m + 1)).1
        rwa [← Function.iterate_add_apply, show m + 1 + n = m + (n + 1) by omega] at this
      rw [show m + 1 + (n + 1) = (m + (n + 1)) + 1 by omega, Function.iterate_succ_apply',
        val_eval_eq_pow v hf hd hB hcoef hB', ih, ← pow_mul, pow_succ]
  have hq' : v (F^[q] c) = v (F^[n + 1] c) ^ (f.natDegree ^ (q - (n + 1))) := by
    have := hpow (q - (n + 1))
    rwa [Nat.sub_add_cancel hq] at this
  have hcq : v c < v (F^[q] c) := by
    rcases le_or_gt (v c) B with hcB | hcB
    · calc v c ≤ B := hcB
        _ < v (F^[n + 1] c) := hγ
        _ ≤ v (F^[q] c) := by
          rw [hq']
          exact le_self_pow (lt_of_le_of_lt hB hγ).le (pow_ne_zero _ (by omega))
    · have hsm : StrictMono fun m : ℕ => v (F^[m] c) :=
        strictMono_nat_of_lt_succ fun m => (val_iterate_of_escape v hf hd hB hcoef hcB m).2
      exact hsm (show 0 < q by omega)
  rw [Valuation.map_sub_eq_of_lt_left v hcq, hq']

end Generic

/-! ### The main lemma -/

section MainLemma

/-- Discreteness of `ℤᵐ⁰`: `exp a < x` forces `exp (a + 1) ≤ x` for `x ≠ 0`. -/
theorem exp_succ_le_of_exp_lt {a : ℤ} {x : WithZero (Multiplicative ℤ)} (hx : x ≠ 0)
    (h : WithZero.exp a < x) : WithZero.exp (a + 1) ≤ x := by
  rw [← WithZero.le_log_iff_exp_le hx]
  rw [← WithZero.lt_log_iff_exp_lt hx] at h
  omega

/-- **Main lemma.** Let `f` be monic of degree `d ≥ 2` over a field `E`. For each index `p` in a
finite type let `w p` be a `ℤᵐ⁰`-valued valuation of `E` and `z p ∈ E` a point that is not
periodic under `f`. If some `z p₀` escapes at `w p₀` and `∏_p w p (f^q(z p) − z p) = 1` for every
`q ≥ 1`, we reach a contradiction. -/
theorem false_of_escapes_of_prod_val_eq_one {E : Type*} [Field E] {f : E[X]} (hf : f.Monic)
    (hd : 2 ≤ f.natDegree)
    {ι : Type*} [Fintype ι] (w : ι → Valuation E (WithZero (Multiplicative ℤ))) (z : ι → E)
    (hper : ∀ p (g : ℕ), 0 < g → (fun x => f.eval x)^[g] (z p) ≠ z p)
    (hesc : ∃ p₀, Escapes (w p₀) f (z p₀))
    (hprod : ∀ q : ℕ, 0 < q → ∏ p, w p ((fun x => f.eval x)^[q] (z p) - z p) = 1) : False := by
  classical
  set F := fun x => f.eval x with hF
  set d := f.natDegree with hd_def
  have hd0 : 0 < d := by omega
  set P : ℕ → ι → E := fun q p => F^[q] (z p) - z p with hP
  have hPne : ∀ q p, 0 < q → P q p ≠ 0 := fun q p hq => sub_ne_zero.mpr (hper p q hq)
  have hwne : ∀ q p, 0 < q → w p (P q p) ≠ 0 :=
    fun q p hq => (Valuation.ne_zero_iff _).mpr (hPne q p hq)
  obtain ⟨p₀, hp₀⟩ := hesc
  haveI : Nonempty ι := ⟨p₀⟩
  obtain ⟨n₀, γ, hγ, hγq⟩ := exists_escape_data (w p₀) hf hd hp₀
  /- Thresholds and bounds for every index. -/
  have key : ∀ p, ∃ (n : ℕ) (B : WithZero (Multiplicative ℤ)), 1 ≤ B ∧
      (Escapes (w p) f (z p) → ∀ q, n ≤ q → 1 < w p (P q p)) ∧
      (¬ Escapes (w p) f (z p) → (∀ q, w p (P q p) ≤ B) ∧ ∀ m, w p (F^[m] (z p)) ≤ B) := by
    intro p
    by_cases hp : Escapes (w p) f (z p)
    · obtain ⟨n, γ', hγ', h⟩ := exists_escape_data (w p) hf hd hp
      refine ⟨n, 1, le_rfl, fun _ q hq => ?_, fun h' => absurd hp h'⟩
      simp only [hP]
      rw [h q hq]
      exact one_lt_pow' hγ' (pow_ne_zero _ (by omega))
    · obtain ⟨B, hB, hcoef⟩ := exists_coef_bound (w p) f
      have h1 : ∀ m, w p (F^[m] (z p)) ≤ B := fun m => by
        by_contra hcon
        push Not at hcon
        exact hp ⟨B, hB, hcoef, m, hcon⟩
      refine ⟨0, B, hB, fun h' => absurd h' hp, fun _ => ⟨fun q => ?_, h1⟩⟩
      exact (Valuation.map_sub _ _ _).trans (max_le (h1 q) (h1 0))
  choose n B hB1 hEsc hBdd using key
  set N : ℕ := (Finset.univ.sup n) ⊔ n₀ ⊔ 1 with hN
  have hNn : ∀ p, n p ≤ N := fun p =>
    (Finset.le_sup (f := n) (Finset.mem_univ p)).trans (le_sup_left.trans le_sup_left)
  have hNn₀ : n₀ ≤ N := le_sup_right.trans le_sup_left
  have hN1 : 1 ≤ N := le_sup_right
  set k := Fintype.card ι with hk
  have hkpos : 0 < k := Fintype.card_pos
  set m : ℕ → ℕ := fun q => d ^ (q - n₀) / k with hm
  have hm_mono : Monotone m := fun a b hab =>
    Nat.div_le_div_right (Nat.pow_le_pow_right hd0 (Nat.sub_le_sub_right hab _))
  /- For large `q` some non-escaping index has `w p (P q p) ≤ exp (−m q)`. -/
  have claim : ∀ q, N ≤ q → k ≤ d ^ (q - n₀) → ∃ p, ¬ Escapes (w p) f (z p) ∧
      w p (P q p) ≤ WithZero.exp (-(m q : ℤ)) := by
    intro q hq hkq
    by_contra hcon
    push Not at hcon
    have hq1 : 0 < q := lt_of_lt_of_le hN1 hq
    have hmq : 1 ≤ m q := (Nat.le_div_iff_mul_le hkpos).mpr (by rw [one_mul]; exact hkq)
    have hlow : ∀ p ∈ Finset.univ.erase p₀,
        WithZero.exp (1 - (m q : ℤ)) ≤ w p (P q p) := by
      intro p _
      have hlt : WithZero.exp (-(m q : ℤ)) < w p (P q p) := by
        by_cases hp : Escapes (w p) f (z p)
        · calc WithZero.exp (-(m q : ℤ)) ≤ 1 := WithZero.exp_le_one_iff.mpr (by omega)
            _ < w p (P q p) := hEsc p hp q ((hNn p).trans hq)
        · exact hcon p hp
      have := exp_succ_le_of_exp_lt (hwne q p hq1) hlt
      rwa [show -(m q : ℤ) + 1 = 1 - (m q : ℤ) by ring] at this
    have hp₀q : WithZero.exp ((d ^ (q - n₀) : ℕ) : ℤ) ≤ w p₀ (P q p₀) := by
      simp only [hP]
      rw [hγq q (hNn₀.trans hq)]
      have hγ0 : γ ≠ 0 := (zero_lt_one.trans hγ).ne'
      rw [← WithZero.le_log_iff_exp_le (pow_ne_zero _ hγ0), WithZero.log_pow]
      have hlogγ : 1 ≤ WithZero.log γ := by
        have : 0 < WithZero.log γ :=
          (WithZero.lt_log_iff_exp_lt hγ0).mpr (by rwa [WithZero.exp_zero])
        omega
      calc ((d ^ (q - n₀) : ℕ) : ℤ) = (d ^ (q - n₀)) • (1 : ℤ) := by simp
        _ ≤ (d ^ (q - n₀)) • WithZero.log γ := nsmul_le_nsmul_right hlogγ _
    have hprodq := hprod q hq1
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ p₀)] at hprodq
    have hlow' : WithZero.exp (1 - (m q : ℤ)) ^ (Finset.univ.erase p₀).card
        ≤ ∏ p ∈ Finset.univ.erase p₀, w p (P q p) := by
      rw [← Finset.prod_const]; exact Finset.prod_le_prod hlow
    rw [Finset.card_erase_of_mem (Finset.mem_univ p₀), Finset.card_univ] at hlow'
    have h1 : WithZero.exp ((d ^ (q - n₀) : ℕ) : ℤ) * WithZero.exp (1 - (m q : ℤ)) ^ (k - 1)
        ≤ 1 := by
      rw [← hprodq]; exact mul_le_mul' hp₀q hlow'
    rw [← WithZero.exp_nsmul, ← WithZero.exp_add, WithZero.exp_le_one_iff, nsmul_eq_mul] at h1
    have hdiv : m q * k ≤ d ^ (q - n₀) := Nat.div_mul_le_self _ _
    obtain ⟨k', hk'⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk', Nat.add_sub_cancel] at h1
    have hdiv' : ((m q : ℤ)) * ((k' : ℤ) + 1) ≤ ((d ^ (q - n₀) : ℕ) : ℤ) := by
      rw [hk'] at hdiv; exact_mod_cast hdiv
    have hmq' : (1 : ℤ) ≤ m q := by exact_mod_cast hmq
    nlinarith
  /- Pigeonhole over `q`. -/
  have hbig : ∀ q, N + k ≤ q → k ≤ d ^ (q - n₀) := by
    intro q hq
    have h1 : q - n₀ < d ^ (q - n₀) := Nat.lt_pow_self (by omega)
    omega
  have hsel : ∀ q : ℕ, ∃ p, ¬ Escapes (w p) f (z p) ∧
      w p (P (N + k + q) p) ≤ WithZero.exp (-(m (N + k + q) : ℤ)) :=
    fun q => claim _ (by omega) (hbig _ (by omega))
  choose sel hselE hselle using hsel
  have hpig : ∀ q : ℕ, ∃ a b : ℕ, a < b ∧ b ≤ k ∧ sel (q + a) = sel (q + b) := by
    intro q
    obtain ⟨a, b, hab, he⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun a : Fin (k + 1) => sel (q + a)) (by simp [hk])
    rcases lt_or_gt_of_ne hab with h | h
    · exact ⟨a, b, h, by omega, he⟩
    · exact ⟨b, a, h, by omega, he.symm⟩
  choose a b hab hbk hsab using hpig
  obtain ⟨⟨p, a₀, b₀⟩, hfib⟩ := Finite.exists_infinite_fiber
    (fun q => (sel (q + a q), (⟨a q, by have := hab q; have := hbk q; omega⟩ : Fin (k + 1)),
      (⟨b q, by have := hbk q; omega⟩ : Fin (k + 1))))
  have hinf := Set.infinite_coe_iff.mp hfib
  set g : ℕ := (b₀ : ℕ) - a₀ with hg
  have hmem : ∀ q, q ∈ (fun q => (sel (q + a q),
      (⟨a q, by have := hab q; have := hbk q; omega⟩ : Fin (k + 1)),
      (⟨b q, by have := hbk q; omega⟩ : Fin (k + 1)))) ⁻¹' {(p, a₀, b₀)} →
      sel (q + a q) = p ∧ a q = a₀ ∧ b q = b₀ := by
    intro q hq
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq, Fin.ext_iff] at hq
    exact hq
  have hgood : ∀ Q : ℕ, ∃ q, Q ≤ q ∧ sel q = p ∧ sel (q + g) = p := by
    intro Q
    obtain ⟨q, hq, hQq⟩ := hinf.exists_gt Q
    obtain ⟨h1, h2, h3⟩ := hmem q hq
    refine ⟨q + a q, by omega, h1, ?_⟩
    have hab' := hab q
    rw [show q + a q + g = q + b q by rw [hg, ← h2, ← h3]; omega, ← hsab q]
    exact h1
  have hg0 : 0 < g := by
    obtain ⟨q, hq⟩ := hinf.nonempty
    obtain ⟨-, h2, h3⟩ := hmem q hq
    have := hab q
    rw [hg, ← h2, ← h3]; omega
  /- The Lipschitz estimate at the index `p` and gap `g`. -/
  obtain ⟨q₁, -, hq₁, -⟩ := hgood 0
  have hpne : ¬ Escapes (w p) f (z p) := hq₁ ▸ hselE q₁
  obtain ⟨-, horbB⟩ := hBdd p hpne
  obtain ⟨Bc, hBc1, hcoefc⟩ := exists_coef_bound (w p) f
  set B' := B p ⊔ Bc with hB'
  have hB'1 : 1 ≤ B' := le_sup_of_le_right hBc1
  have hcoef' : ∀ j < f.natDegree, w p (f.coeff j) ≤ B' :=
    fun j hj => (hcoefc j hj).trans le_sup_right
  have horb' : ∀ mm, w p (F^[mm] (z p)) ≤ B' := fun mm => (horbB mm).trans le_sup_left
  set L : WithZero (Multiplicative ℤ) := (B' ^ f.natDegree) ^ g with hL
  have hL1 : 1 ≤ L := one_le_pow_of_one_le' (one_le_pow_of_one_le' hB'1 _) _
  have hL0 : L ≠ 0 := (zero_lt_one.trans_le hL1).ne'
  have hest : ∀ q, sel q = p → sel (q + g) = p →
      w p (F^[g] (z p) - z p) ≤ WithZero.exp (-(m (N + k + q) : ℤ)) * L := by
    intro q h1 h2
    have e1 := hselle q
    rw [h1] at e1
    have e2 := hselle (q + g)
    rw [h2] at e2
    have hdecomp : F^[g] (z p) - z p
        = (F^[g] (z p) - F^[g] (F^[N + k + q] (z p))) + P (N + k + (q + g)) p := by
      simp only [hP]
      rw [← Function.iterate_add_apply, show g + (N + k + q) = N + k + (q + g) by omega]; ring
    rw [hdecomp]
    refine (Valuation.map_add _ _ _).trans (max_le ?_ ?_)
    · have hlip := val_iterate_sub_iterate_le (w p) hf hB'1 hcoef' (x := z p)
        (y := F^[N + k + q] (z p)) horb'
        (fun mm => by rw [← Function.iterate_add_apply]; exact horb' _) g
      refine hlip.trans ?_
      rw [Valuation.map_sub_swap]
      exact mul_le_mul' e1 le_rfl
    · refine e2.trans ?_
      calc WithZero.exp (-(m (N + k + (q + g)) : ℤ))
          ≤ WithZero.exp (-(m (N + k + q) : ℤ)) := by
            rw [WithZero.exp_le_exp]
            have := hm_mono (show N + k + q ≤ N + k + (q + g) by omega)
            omega
        _ = WithZero.exp (-(m (N + k + q) : ℤ)) * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul' le_rfl hL1
  have hy0 : w p (F^[g] (z p) - z p) ≠ 0 := hwne g p hg0
  set t : ℤ := WithZero.log L - WithZero.log (w p (F^[g] (z p) - z p)) + 1 with ht
  obtain ⟨q, hq, h1, h2⟩ := hgood (k * t.toNat)
  have hmq : t.toNat ≤ m (N + k + q) := by
    simp only [hm]
    rw [Nat.le_div_iff_mul_le hkpos]
    have h3 := Nat.lt_pow_self (n := N + k + q - n₀) (show 1 < d by omega)
    have h4 : t.toNat * k ≤ N + k + q - n₀ := by
      rw [mul_comm]; omega
    omega
  have hfin := hest q h1 h2
  rw [← WithZero.exp_log hL0, ← WithZero.exp_add, ← WithZero.log_le_iff_le_exp hy0] at hfin
  have h5 := Int.self_le_toNat t
  omega

end MainLemma

end IngramMello
