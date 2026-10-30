import BC4lean.ReducedGroupCStar

/-! # The reduced group C⋆-algebra of a finite group

For a finite group the integrated regular representation is onto the reduced group
C⋆-algebra: its range is finite-dimensional, hence closed, and it is dense. So the reduced
group C⋆-algebra of a finite group is the group algebra with its involution.

For a group with exactly two elements the trivial and the sign character together identify the
group algebra, and hence the reduced group C⋆-algebra, with `ℂ × ℂ`.
-/

noncomputable section

namespace BC4lean

section Finite

variable {Γ : Type*} [Group Γ] [Finite Γ]

/-- For a finite group the integrated regular representation is onto the reduced group
C⋆-algebra. -/
theorem integratedToReduced_surjective :
    Function.Surjective (integratedToReduced (Γ := Γ)) := by
  have hrange : Set.range (integratedToReduced (Γ := Γ)) =
      (LinearMap.range (integratedToReduced (Γ := Γ)).toAlgHom.toLinearMap : Set _) := by
    ext x
    simp
  have hclosed : IsClosed (Set.range (integratedToReduced (Γ := Γ))) := by
    rw [hrange]
    exact Submodule.closed_of_finiteDimensional _
  intro T
  have hT : T ∈ closure (Set.range (integratedToReduced (Γ := Γ))) := by
    rw [(denseRange_integratedToReduced (Γ := Γ)).closure_range]
    trivial
  rwa [hclosed.closure_eq] at hT

/-- For a finite group the reduced group C⋆-algebra is the group algebra. -/
def finiteReducedEquiv : GroupAlgebra Γ ≃⋆ₐ[ℂ] ReducedGroupCStar Γ :=
  StarAlgEquiv.ofBijective integratedToReduced
    ⟨integratedToReduced_injective, integratedToReduced_surjective⟩

@[simp] theorem finiteReducedEquiv_apply (a : GroupAlgebra Γ) :
    finiteReducedEquiv a = integratedToReduced a := rfl

theorem finiteReducedEquiv_delta (g : Γ) :
    finiteReducedEquiv (GroupAlgebra.delta g) =
      ⟨regularOperator g, regularOperator_mem_reducedAlgebra g⟩ :=
  Subtype.ext (integratedRepresentation_delta g)

end Finite

section OrderTwo

variable {Γ : Type*} [Group Γ]

private theorem finite_of_card_eq_two {α : Type*} (h2 : Nat.card α = 2) : Finite α :=
  Nat.finite_of_card_ne_zero (by simp [h2])

private theorem eq_of_ne_one_of_card_eq_two (h2 : Nat.card Γ = 2) {g h : Γ} (hg : g ≠ 1)
    (hh : h ≠ 1) : g = h :=
  ((Nat.card_eq_two_iff' (1 : Γ)).1 h2).unique hg hh

private theorem mul_self_eq_one_of_card_eq_two (h2 : Nat.card Γ = 2) (g : Γ) : g * g = 1 := by
  simpa [← pow_two, h2] using pow_card_eq_one' (x := g)

open scoped Classical in
/-- The sign character of a group of order two: `1` at the identity and `-1` elsewhere.

The case split uses classical decidability of `g = 1`; use `orderTwoSign_one` and
`orderTwoSign_of_ne_one` rather than unfolding the definition. -/
def orderTwoSign (h2 : Nat.card Γ = 2) : Γ →* ℂ where
  toFun g := if g = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' g h := by
    by_cases hg : g = 1
    · simp [hg]
    by_cases hh : h = 1
    · simp [hh]
    have hgh : g * h = 1 := by
      rw [← eq_of_ne_one_of_card_eq_two h2 hg hh, mul_self_eq_one_of_card_eq_two h2]
    simp [hg, hh, hgh]

theorem orderTwoSign_one (h2 : Nat.card Γ = 2) : orderTwoSign h2 1 = 1 :=
  map_one _

theorem orderTwoSign_of_ne_one (h2 : Nat.card Γ = 2) {g : Γ} (hg : g ≠ 1) :
    orderTwoSign h2 g = -1 := by
  classical
  simp [orderTwoSign, hg]

theorem star_orderTwoSign (h2 : Nat.card Γ = 2) (g : Γ) :
    star (orderTwoSign h2 g) = orderTwoSign h2 g := by
  by_cases hg : g = 1
  · simp [hg]
  · simp [orderTwoSign_of_ne_one h2 hg]

theorem orderTwoSign_inv (h2 : Nat.card Γ = 2) (g : Γ) :
    orderTwoSign h2 g⁻¹ = orderTwoSign h2 g := by
  rw [inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_card_eq_two h2 g)]

/-- The trivial and the sign character on the group algebra of a group of order two. -/
def orderTwoCharacters (h2 : Nat.card Γ = 2) : GroupAlgebra Γ →⋆ₐ[ℂ] ℂ × ℂ where
  toAlgHom := MonoidAlgebra.lift ℂ (ℂ × ℂ) Γ ((1 : Γ →* ℂ).prod (orderTwoSign h2))
  map_star' a := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      simp only [AlgHom.toFun_eq_coe, star_add, map_add] at ha hb ⊢
      rw [ha, hb]
    | single g z =>
      change MonoidAlgebra.lift ℂ (ℂ × ℂ) Γ _ (GroupAlgebra.involution _) = _
      rw [GroupAlgebra.involution_single]
      ext <;> simp [orderTwoSign_inv, star_orderTwoSign, mul_comm]

@[simp] theorem orderTwoCharacters_single (h2 : Nat.card Γ = 2) (g : Γ) (z : ℂ) :
    orderTwoCharacters h2 (MonoidAlgebra.single g z) = (z, z * orderTwoSign h2 g) := by
  simp [orderTwoCharacters]

theorem orderTwoCharacters_delta (h2 : Nat.card Γ = 2) (g : Γ) :
    orderTwoCharacters h2 (GroupAlgebra.delta g) = (1, orderTwoSign h2 g) := by
  simp [GroupAlgebra.delta]

theorem orderTwoCharacters_surjective (h2 : Nat.card Γ = 2) :
    Function.Surjective (orderTwoCharacters h2) := by
  obtain ⟨g, hg, -⟩ := (Nat.card_eq_two_iff' (1 : Γ)).1 h2
  rintro ⟨z, w⟩
  refine ⟨MonoidAlgebra.single 1 ((z + w) / 2) + MonoidAlgebra.single g ((z - w) / 2), ?_⟩
  rw [map_add, orderTwoCharacters_single, orderTwoCharacters_single, orderTwoSign_one,
    orderTwoSign_of_ne_one h2 hg]
  ext <;> simp <;> ring

theorem orderTwoCharacters_injective (h2 : Nat.card Γ = 2) :
    Function.Injective (orderTwoCharacters h2) := by
  have := finite_of_card_eq_two h2
  have : Fintype Γ := Fintype.ofFinite Γ
  have hrank : Module.finrank ℂ (GroupAlgebra Γ) = Module.finrank ℂ (ℂ × ℂ) := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis Γ ℂ), Fintype.card_eq_nat_card, h2,
      Module.finrank_prod, Module.finrank_self]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (orderTwoCharacters h2).toAlgHom.toLinearMap) hrank).2
    (orderTwoCharacters_surjective h2)

/-- The group algebra of a group of order two is `ℂ × ℂ`, by its two characters. -/
def orderTwoGroupAlgebraEquiv (h2 : Nat.card Γ = 2) : GroupAlgebra Γ ≃⋆ₐ[ℂ] ℂ × ℂ :=
  StarAlgEquiv.ofBijective (orderTwoCharacters h2)
    ⟨orderTwoCharacters_injective h2, orderTwoCharacters_surjective h2⟩

@[simp] theorem orderTwoGroupAlgebraEquiv_apply (h2 : Nat.card Γ = 2) (a : GroupAlgebra Γ) :
    orderTwoGroupAlgebraEquiv h2 a = orderTwoCharacters h2 a := rfl

/-- For a group of order two, `(z, w) ↦ z P₊ + w P₋` with `P± = (1 ± λ_g) / 2` is a
⋆-isomorphism `ℂ × ℂ ≃ C*_r(Γ)`. -/
def orderTwoReducedEquiv (h2 : Nat.card Γ = 2) : ℂ × ℂ ≃⋆ₐ[ℂ] ReducedGroupCStar Γ :=
  haveI := finite_of_card_eq_two h2
  (orderTwoGroupAlgebraEquiv h2).symm.trans finiteReducedEquiv

theorem orderTwoReducedEquiv_symm_regularOperator (h2 : Nat.card Γ = 2) (g : Γ) :
    (orderTwoReducedEquiv h2).symm ⟨regularOperator g, regularOperator_mem_reducedAlgebra g⟩ =
      (1, orderTwoSign h2 g) := by
  have := finite_of_card_eq_two h2
  rw [StarAlgEquiv.symm_apply_eq, ← orderTwoCharacters_delta, ← orderTwoGroupAlgebraEquiv_apply,
    orderTwoReducedEquiv, StarAlgEquiv.trans_apply, StarAlgEquiv.symm_apply_apply,
    finiteReducedEquiv_delta]

/-- The non-identity element goes to `(1, -1)`. -/
theorem orderTwoReducedEquiv_symm_regularOperator_of_ne_one (h2 : Nat.card Γ = 2) {g : Γ}
    (hg : g ≠ 1) :
    (orderTwoReducedEquiv h2).symm ⟨regularOperator g, regularOperator_mem_reducedAlgebra g⟩ =
      (1, -1) := by
  rw [orderTwoReducedEquiv_symm_regularOperator, orderTwoSign_of_ne_one h2 hg]

/-- The isomorphism sends `(z, w)` to `z P₊ + w P₋ = ((z + w) / 2) • 1 + ((z - w) / 2) • λ_g`,
where `g` is the element other than the identity. -/
theorem orderTwoReducedEquiv_apply (h2 : Nat.card Γ = 2) {g : Γ} (hg : g ≠ 1) (z w : ℂ) :
    orderTwoReducedEquiv h2 (z, w) =
      ((z + w) / 2) • (1 : ReducedGroupCStar Γ) +
        ((z - w) / 2) • ⟨regularOperator g, regularOperator_mem_reducedAlgebra g⟩ := by
  rw [eq_comm, ← StarAlgEquiv.symm_apply_eq, map_add, map_smul, map_smul, map_one,
    orderTwoReducedEquiv_symm_regularOperator_of_ne_one h2 hg]
  ext <;> simp <;> ring

end OrderTwo

end BC4lean
