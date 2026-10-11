import IngramMello.Cited

/-!
# Lemma 4: one fixed linear form

From Dvornicich–Zannier: for a number field `K` and a bound `B` there is a single
linear form `Λ(y) = ∑ e_i y_i` with `e_i ∈ K` such that every algebraic integer of
`K^cyc` with house `≤ B` is a value of `Λ` at a point of `(μ_∞ ∪ {0})^m`.
-/

namespace IngramMello

/-- Pad a sum over `Fin n` to a sum over `Fin N` when `n ≤ N`. -/
theorem sum_fin_pad {M : Type*} [AddCommMonoid M] {n N : ℕ} (hn : n ≤ N) (g : Fin n → M) :
    ∑ i, g i = ∑ k : Fin N, if h : (k : ℕ) < n then g ⟨k, h⟩ else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => if h : k < n then g ⟨k, h⟩ else 0) N]
  rw [← Finset.sum_range_add_sum_Ico _ hn]
  rw [Finset.sum_eq_zero (s := Finset.Ico n N) (fun k hk => by
    simp only [Finset.mem_Ico] at hk
    simp [not_lt.2 hk.1]), add_zero]
  rw [← Fin.sum_univ_eq_sum_range (fun k => if h : k < n then g ⟨k, h⟩ else 0) n]
  simp

/-- **Lemma 4** (fixed linear form), from Dvornicich–Zannier. -/
theorem exists_linearForm (hDZ : DvornicichZannier) (K : IntermediateField ℚ ℂ)
    (hK : FiniteDimensional ℚ K) (B : ℝ) :
    ∃ (m : ℕ) (e : Fin m → ℂ), (∀ i, e i ∈ K) ∧
      ∀ α ∈ Kcyc K, IsIntegral ℤ α → HouseLE α B →
        ∃ y : Fin m → ℂ, (∀ i, y i = 0 ∨ IsRootOfUnityC (y i)) ∧ α = ∑ i, e i * y i := by
  classical
  obtain ⟨E, hE, N, hN⟩ := hDZ K hK B
  let ι := {x : ℂ // x ∈ E} × Fin N
  let σ := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun i => ((σ.symm i).1 : ℂ), fun i => hE _ (σ.symm i).1.2, ?_⟩
  intro α hα hint hB
  obtain ⟨n, c, ξ, hnN, hc, hξ, rfl⟩ := hN α hα hint hB
  let y : ι → ℂ := fun p =>
    if h : (p.2 : ℕ) < n then (if c ⟨p.2, h⟩ = p.1 then ξ ⟨p.2, h⟩ else 0) else 0
  refine ⟨fun i => y (σ.symm i), fun i => ?_, ?_⟩
  · simp only [y]
    split_ifs
    · exact Or.inr (hξ _)
    · exact Or.inl rfl
    · exact Or.inl rfl
  · rw [Equiv.sum_comp σ.symm (fun p : ι => ((p.1 : ℂ)) * y p)]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    rw [sum_fin_pad hnN]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : (k : ℕ) < n
    · simp only [y, h, dite_true]
      rw [Finset.sum_eq_single (⟨c ⟨k, h⟩, hc _⟩ : {x : ℂ // x ∈ E})]
      · simp
      · intro b _ hb
        have : c ⟨k, h⟩ ≠ b := fun h' => hb (Subtype.ext h'.symm)
        simp [this]
      · simp
    · simp [y, h]

end IngramMello
