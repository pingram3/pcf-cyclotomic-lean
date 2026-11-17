import IngramMello.LaurentOrder

/-!
# Lemma 5 (Hajós' lemma)

A nonzero Laurent polynomial `F ∈ ℂ[u₁^{±1}, …, u_r^{±1}]` with at most `T` monomials has
order at most `T - 1` at every point `x ∈ (ℂ^×)^r`, i.e. `F ∉ 𝔪_x ^ T`.

The paper restricts to a monomial curve `t ↦ x t^s` and differentiates in one variable. We
instead use the Euler derivation `D_w` on `ℂ[ℤ^r]` directly (its pullback along the curve is
`t d/dt`). Induct on `T`: pick a monomial `u^a` of `F` and a weight `w` with `w(b) ≠ w(a)`
for every other exponent `b` of `F`. Then `D_w F - w(a) F` has one monomial fewer and order
at least `ord_x F - 1`. If it vanishes, `F` is a single monomial, a unit.
-/

namespace IngramMello

open AddMonoidAlgebra

namespace MvLaurent

variable {r : ℕ}

/-- For finitely many exponents `b ≠ a`, there is an additive weight `w : ℤ^r → ℂ` with
`w b ≠ w a` for all of them. -/
theorem exists_weight_ne (a : Fin r → ℤ) (S : Finset (Fin r → ℤ)) (ha : a ∉ S) :
    ∃ w : (Fin r → ℤ) →+ ℂ, ∀ b ∈ S, w b ≠ w a := by
  let v : S → (Fin r → ℂ) := fun b j => ((b.1 j - a j : ℤ) : ℂ)
  have hv : ∀ b, v b ≠ 0 := by
    rintro ⟨b, hb⟩ h
    apply ha
    have : b = a := funext fun j => by
      have := congrFun h j
      simp only [v, Pi.zero_apply, Int.cast_eq_zero, sub_eq_zero] at this
      exact this
    exact this ▸ hb
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℂ) v hv
  refine ⟨{ toFun := fun b => f fun j => (b j : ℂ), map_zero' := ?_, map_add' := ?_ }, ?_⟩
  · convert f.map_zero using 2; funext j; simp
  · intro b c
    rw [← map_add]
    congr 1
    funext j
    simp
  · intro b hb h
    apply hf ⟨b, hb⟩
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk] at h
    have : v ⟨b, hb⟩ = (fun j => (b j : ℂ)) - fun j => (a j : ℂ) := by
      funext j
      simp [v]
    rw [this, map_sub, h, sub_self]

/-- **Lemma 5 (Hajós).** If `F ≠ 0` has at most `T` monomials, then `ord_x F ≤ T - 1` at
every `x ∈ (ℂ^×)^r`, i.e. `F ∉ 𝔪_x ^ T`. -/
theorem hajos (x : Fin r → ℂˣ) (T : ℕ) (F : MvLaurent r) (hF : F ≠ 0)
    (hT : F.coeff.support.card ≤ T) : F ∉ maxIdeal x ^ T := by
  induction T generalizing F with
  | zero =>
    exact absurd (by simpa using hT) hF
  | succ T ih =>
    intro hmem
    obtain ⟨a, ha⟩ : F.coeff.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, Finsupp.support_eq_empty, coeff_eq_zero]
      exact hF
    set S := F.coeff.support.erase a
    obtain ⟨w, hw⟩ := exists_weight_ne a S (Finset.notMem_erase a _)
    set G := eulerD w F - w a • F with hG
    have hGcoeff : ∀ b, G.coeff b = (w b - w a) * F.coeff b := fun b => by
      simp [hG, sub_mul]
    have hGmem : G ∈ maxIdeal x ^ T :=
      sub_mem (eulerD_mem_pow w _ T F hmem)
        (Submodule.smul_of_tower_mem _ _ (Ideal.pow_le_pow_right T.le_succ hmem))
    have hGsupp : G.coeff.support ⊆ S := fun b hb => by
      rw [Finsupp.mem_support_iff, hGcoeff] at hb
      refine Finset.mem_erase.2 ⟨fun hba => ?_, Finsupp.mem_support_iff.2 (right_ne_zero_of_mul hb)⟩
      subst hba
      simp at hb
    by_cases hG0 : G = 0
    · -- `F` is a single monomial, hence a unit, but it lies in `𝔪_x`.
      have hS : S = ∅ := Finset.eq_empty_of_forall_notMem fun b hb => by
        have h := hGcoeff b
        rw [hG0, coeff_zero, Finsupp.zero_apply, eq_comm, mul_eq_zero, sub_eq_zero] at h
        rcases h with h | h
        · exact hw b hb h
        · exact Finsupp.mem_support_iff.1 (Finset.mem_of_mem_erase hb) h
      have hsupp : F.coeff.support = {a} := by
        rw [← Finset.insert_erase ha]
        simp [S] at hS
        simp [hS]
      obtain ⟨hFa, hFeq⟩ := Finsupp.support_eq_singleton.1 hsupp
      have hF1 : F ∈ maxIdeal x := Ideal.pow_le_self T.succ_ne_zero hmem
      have : F = single a (F.coeff a) := by
        rw [← coeff_inj, coeff_single]
        exact hFeq
      rw [this] at hF1
      exact single_notMem_maxIdeal x a hFa hF1
    · refine ih G hG0 ?_ hGmem
      calc G.coeff.support.card ≤ S.card := Finset.card_le_card hGsupp
        _ = F.coeff.support.card - 1 := Finset.card_erase_of_mem ha
        _ ≤ T := by omega

/-- A sum of `n` monomials has at most `n` exponents in its support. -/
theorem card_support_sum_single_le {n : ℕ} (a : Fin n → Fin r → ℤ) (β : Fin n → ℂ) :
    (∑ i, single (a i) (β i)).coeff.support.card ≤ n := by
  rw [coeff_sum]
  calc (∑ i, (single (a i) (β i)).coeff).support.card
      ≤ (Finset.univ.biUnion fun i => (single (a i) (β i)).coeff.support).card :=
        Finset.card_le_card (Finsupp.support_finsetSum)
    _ ≤ ∑ i, (single (a i) (β i)).coeff.support.card := Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin n, 1 := Finset.sum_le_sum fun i _ => by
        rw [coeff_single]
        exact (Finset.card_le_card Finsupp.support_single_subset).trans (by simp)
    _ = n := by simp

/-- **Lemma 5 (Hajós)**, in the form used in Lemma 9: a nonzero sum of at most `T`
monomials `βᵢ u^{aᵢ}` (repetitions allowed) does not lie in `𝔪_x ^ T`. -/
theorem hajos_sum (x : Fin r → ℂˣ) {T n : ℕ} (hn : n ≤ T) (a : Fin n → Fin r → ℤ)
    (β : Fin n → ℂ) (hF : ∑ i, single (a i) (β i) ≠ 0) :
    ∑ i, single (a i) (β i) ∉ maxIdeal x ^ T :=
  hajos x T _ hF ((card_support_sum_single_le a β).trans hn)

end MvLaurent

end IngramMello
