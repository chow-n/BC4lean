import BC4lean.FiniteAbelianCharacterProjection
import BC4lean.OperatorKProductEquiv
import BC4lean.OperatorKFinitePi
import BC4lean.FiniteReducedGroupCStar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

/-! # The reduced C⋆-algebra of a finite abelian group, and K-theory of `ℂ^ι`

* `piOperatorK0Equiv`, `piOperatorK1Equiv`: for a finite type `ι`,
  `K_p(ι → ℂ) ≃+ (ι → K_p(ℂ))`, `y ↦ (i ↦ (eval_i)_* y)`, with inverse
  `v ↦ ∑_i (single_i)_* (v i)`. The identity `∑_i (single_i)_* (eval_i)_* y = y` is proved for
  `ι = Fin n` by induction on `n` through `ℂ^{n+1} ≅ ℂ × ℂ^n` (`piFinSuccStarAlgEquiv`) and the
  product decomposition `operatorK0ProductEquiv` / `operatorK1ProductEquiv`, then transported along
  `ι ≃ Fin n`. These are `k0PiEquiv` / `k1PiEquiv` of `OperatorKFinitePi` for the constant family
  `ℂ`, read on operator K-groups and with the coordinate maps made explicit, which is what the
  assembly computation needs.
* For a finite abelian group `Γ`, `δ_g ↦ (ψ ↦ conj ψ(g))` is a ⋆-isomorphism
  `GroupAlgebra Γ ≃⋆ₐ (Γ̂ → ℂ)` (`finiteAbelianGroupAlgebraEquiv`); it sends the group-algebra
  character projection `|Γ|⁻¹ ∑_g χ(g) δ_g` to the coordinate idempotent `single χ 1`.
  Composed with `finiteReducedEquiv`, this gives `(Γ̂ → ℂ) ≃⋆ₐ C*_r(Γ)`
  (`finiteAbelianReducedEquiv`). For `|Γ| = 2` it is `orderTwoReducedEquiv` up to the order of
  the two coordinates. -/

noncomputable section

namespace BC4lean.OperatorKTheory

section Pi

variable (ι : Type)

/-- Evaluation at a coordinate. -/
def piEvalHom (i : ι) : (ι → ℂ) →⋆ₙₐ[ℂ] ℂ where
  toFun f := f i
  map_smul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
  map_star' _ := rfl

@[simp] theorem piEvalHom_apply (i : ι) (f : ι → ℂ) : piEvalHom ι i f = f i := rfl

/-- Reindex `ℂ^ι` along an equivalence. -/
def piCongrScalarEquiv {κ : Type} (e : ι ≃ κ) : (ι → ℂ) ≃⋆ₐ[ℂ] (κ → ℂ) where
  toFun f k := f (e.symm k)
  invFun f i := f (e i)
  left_inv f := by funext i; simp
  right_inv f := by funext k; simp
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_star' _ := rfl
  map_smul' _ _ := rfl

variable [DecidableEq ι]

/-- The coordinate embedding `z ↦ single i z`. -/
def piSingleHom (i : ι) : ℂ →⋆ₙₐ[ℂ] (ι → ℂ) where
  toFun z := (Pi.single i z : ι → ℂ)
  map_smul' z w := by
    funext j
    rcases eq_or_ne j i with rfl | h <;> simp [*]
  map_zero' := by
    funext j
    rcases eq_or_ne j i with rfl | h <;> simp [*]
  map_add' z w := by
    funext j
    rcases eq_or_ne j i with rfl | h <;> simp [*]
  map_mul' z w := by
    funext j
    rcases eq_or_ne j i with rfl | h <;> simp [*]
  map_star' z := by
    funext j
    rcases eq_or_ne j i with rfl | h <;> simp [*]

@[simp] theorem piSingleHom_apply (i : ι) (z : ℂ) :
    piSingleHom ι i z = (Pi.single i z : ι → ℂ) := rfl

theorem piEvalHom_comp_piSingleHom_self (i : ι) :
    (piEvalHom ι i).comp (piSingleHom ι i) = NonUnitalStarAlgHom.id ℂ ℂ := by
  ext z
  simp

theorem piEvalHom_comp_piSingleHom_of_ne {i j : ι} (h : i ≠ j) :
    (piEvalHom ι j).comp (piSingleHom ι i) = 0 := by
  ext z
  simp [Pi.single_eq_of_ne h.symm]

end Pi

section K0

theorem operatorK0Map_apply_apply {A B C : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C] (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B)
    (x : OperatorK0 A) : operatorK0Map ψ (operatorK0Map φ x) = operatorK0Map (ψ.comp φ) x := by
  rw [operatorK0Map_comp]
  rfl

theorem operatorK0_eq_of_starAlgEquiv {A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B) (y : OperatorK0 A) :
    operatorK0Map e.symm.toNonUnitalStarAlgHom (operatorK0Map e.toNonUnitalStarAlgHom y) = y := by
  rw [operatorK0Map_apply_apply]
  have h : e.symm.toNonUnitalStarAlgHom.comp e.toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.id ℂ A := by
    ext a
    exact e.symm_apply_apply a
  rw [h, operatorK0Map_id]
  rfl

/-- `∑_i (single_i)_* (eval_i)_* y = y` on `K₀(ℂ^n)`. -/
theorem sum_piSingle_piEval_fin_k0 : ∀ (n : ℕ) (y : OperatorK0 (Fin n → ℂ)),
    ∑ i, operatorK0Map (piSingleHom (Fin n) i) (operatorK0Map (piEvalHom (Fin n) i) y) = y
  | 0, y => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    have h : NonUnitalStarAlgHom.id ℂ (Fin 0 → ℂ) = 0 := by
      ext f i
      exact i.elim0
    rw [← AddMonoidHom.id_apply (OperatorK0 (Fin 0 → ℂ)) y, ← operatorK0Map_id, h,
      operatorK0Map_zero]
    rfl
  | n + 1, y => by
    let e := piFinSuccStarAlgEquiv fun _ : Fin (n + 1) => ℂ
    have hz := (operatorK0ProductEquiv ℂ (Fin n → ℂ)).symm_apply_apply
      (operatorK0Map e.toNonUnitalStarAlgHom y)
    rw [operatorK0ProductEquiv_apply, operatorK0ProductEquiv_symm_apply,
      ← sum_piSingle_piEval_fin_k0 n (operatorK0Map (StarAlgHom.snd ℂ ℂ (Fin n → ℂ)).toNonUnitalStarAlgHom
        (operatorK0Map e.toNonUnitalStarAlgHom y))] at hz
    conv_rhs => rw [← operatorK0_eq_of_starAlgEquiv e y, ← hz]
    rw [map_add, map_sum, map_sum, Fin.sum_univ_succ]
    simp only [operatorK0Map_apply_apply]
    congr 1
    · refine congrArg (fun φ => operatorK0Map φ y) (NonUnitalStarAlgHom.ext fun f => ?_)
      funext j
      change (Pi.single (0 : Fin (n + 1)) (f 0) : Fin (n + 1) → ℂ) j =
        (Fin.cons (f 0) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) j
      refine Fin.cases ?_ (fun k => ?_) j
      · rw [Pi.single_eq_same, Fin.cons_zero]
      · rw [Pi.single_eq_of_ne (Fin.succ_ne_zero k), Fin.cons_succ, Pi.zero_apply]
    · refine Finset.sum_congr rfl fun i _ => ?_
      refine congrArg (fun φ => operatorK0Map φ y) (NonUnitalStarAlgHom.ext fun f => ?_)
      funext j
      change (Pi.single i.succ (f i.succ) : Fin (n + 1) → ℂ) j =
        (Fin.cons (0 : ℂ) (Pi.single i (f i.succ) : Fin n → ℂ) : Fin (n + 1) → ℂ) j
      refine Fin.cases ?_ (fun k => ?_) j
      · rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm, Fin.cons_zero]
      · rw [Fin.cons_succ]
        rcases eq_or_ne k i with rfl | h
        · rw [Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne ((Fin.succ_injective _).ne h)]

variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-- `∑_i (single_i)_* (eval_i)_* y = y` on `K₀(ℂ^ι)`. -/
theorem sum_piSingle_piEval_k0 (y : OperatorK0 (ι → ℂ)) :
    ∑ i, operatorK0Map (piSingleHom ι i) (operatorK0Map (piEvalHom ι i) y) = y := by
  let e := Fintype.equivFin ι
  let σ := piCongrScalarEquiv ι e
  have h := congrArg (operatorK0Map σ.symm.toNonUnitalStarAlgHom)
    (sum_piSingle_piEval_fin_k0 (Fintype.card ι) (operatorK0Map σ.toNonUnitalStarAlgHom y))
  rw [operatorK0_eq_of_starAlgEquiv, map_sum] at h
  conv_rhs => rw [← h]
  simp only [operatorK0Map_apply_apply]
  refine (Fintype.sum_equiv e _ _ fun i => ?_)
  refine congrArg (fun φ => operatorK0Map φ y) (NonUnitalStarAlgHom.ext fun f => ?_)
  funext j
  simp only [NonUnitalStarAlgHom.coe_comp, Function.comp_apply, piEvalHom_apply,
    piSingleHom_apply]
  change (Pi.single i (f i) : ι → ℂ) j =
    (Pi.single (e i) (f (e.symm (e i))) : Fin (Fintype.card ι) → ℂ) (e j)
  rw [Equiv.symm_apply_apply]
  rcases eq_or_ne j i with rfl | hji
  · simp
  · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne (e.injective.ne hji)]

/-- `(eval_j)_* ∑_i (single_i)_* v_i = v_j` on `K₀`. -/
theorem piEval_sum_piSingle_k0 (v : ι → OperatorK0 ℂ) (j : ι) :
    operatorK0Map (piEvalHom ι j) (∑ i, operatorK0Map (piSingleHom ι i) (v i)) = v j := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [operatorK0Map_apply_apply, piEvalHom_comp_piSingleHom_self, operatorK0Map_id]
    rfl
  · intro _ _ hij
    rw [operatorK0Map_apply_apply, piEvalHom_comp_piSingleHom_of_ne ι hij, operatorK0Map_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `K₀(ℂ^ι) ≃+ K₀(ℂ)^ι`, by the coordinate evaluations, with inverse the sum of the coordinate
embeddings. -/
def piOperatorK0Equiv : OperatorK0 (ι → ℂ) ≃+ (ι → OperatorK0 ℂ) where
  toFun y i := operatorK0Map (piEvalHom ι i) y
  invFun v := ∑ i, operatorK0Map (piSingleHom ι i) (v i)
  left_inv y := sum_piSingle_piEval_k0 ι y
  right_inv v := funext fun j => piEval_sum_piSingle_k0 ι v j
  map_add' y z := funext fun _ => map_add _ y z

theorem piOperatorK0Equiv_symm_apply (v : ι → OperatorK0 ℂ) :
    (piOperatorK0Equiv ι).symm v = ∑ i, operatorK0Map (piSingleHom ι i) (v i) := rfl

end K0

section K1

theorem operatorK1Map_apply_apply {A B C : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra C] (ψ : B →⋆ₙₐ[ℂ] C) (φ : A →⋆ₙₐ[ℂ] B)
    (x : OperatorK1 A) : operatorK1Map ψ (operatorK1Map φ x) = operatorK1Map (ψ.comp φ) x := by
  rw [operatorK1Map_comp]
  rfl

theorem operatorK1_eq_of_starAlgEquiv {A B : Type*} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] (e : A ≃⋆ₐ[ℂ] B) (y : OperatorK1 A) :
    operatorK1Map e.symm.toNonUnitalStarAlgHom (operatorK1Map e.toNonUnitalStarAlgHom y) = y := by
  rw [operatorK1Map_apply_apply]
  have h : e.symm.toNonUnitalStarAlgHom.comp e.toNonUnitalStarAlgHom =
      NonUnitalStarAlgHom.id ℂ A := by
    ext a
    exact e.symm_apply_apply a
  rw [h, operatorK1Map_id]
  rfl

/-- `∑_i (single_i)_* (eval_i)_* y = y` on `K₁(ℂ^n)`. -/
theorem sum_piSingle_piEval_fin_k1 : ∀ (n : ℕ) (y : OperatorK1 (Fin n → ℂ)),
    ∑ i, operatorK1Map (piSingleHom (Fin n) i) (operatorK1Map (piEvalHom (Fin n) i) y) = y
  | 0, y => by
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    have h : NonUnitalStarAlgHom.id ℂ (Fin 0 → ℂ) = 0 := by
      ext f i
      exact i.elim0
    rw [← AddMonoidHom.id_apply (OperatorK1 (Fin 0 → ℂ)) y, ← operatorK1Map_id, h,
      operatorK1Map_zero]
    rfl
  | n + 1, y => by
    let e := piFinSuccStarAlgEquiv fun _ : Fin (n + 1) => ℂ
    have hz := (operatorK1ProductEquiv ℂ (Fin n → ℂ)).symm_apply_apply
      (operatorK1Map e.toNonUnitalStarAlgHom y)
    rw [operatorK1ProductEquiv_apply, operatorK1ProductEquiv_symm_apply,
      ← sum_piSingle_piEval_fin_k1 n (operatorK1Map (StarAlgHom.snd ℂ ℂ (Fin n → ℂ)).toNonUnitalStarAlgHom
        (operatorK1Map e.toNonUnitalStarAlgHom y))] at hz
    conv_rhs => rw [← operatorK1_eq_of_starAlgEquiv e y, ← hz]
    rw [map_add, map_sum, map_sum, Fin.sum_univ_succ]
    simp only [operatorK1Map_apply_apply]
    congr 1
    · refine congrArg (fun φ => operatorK1Map φ y) (NonUnitalStarAlgHom.ext fun f => ?_)
      funext j
      change (Pi.single (0 : Fin (n + 1)) (f 0) : Fin (n + 1) → ℂ) j =
        (Fin.cons (f 0) (0 : Fin n → ℂ) : Fin (n + 1) → ℂ) j
      refine Fin.cases ?_ (fun k => ?_) j
      · rw [Pi.single_eq_same, Fin.cons_zero]
      · rw [Pi.single_eq_of_ne (Fin.succ_ne_zero k), Fin.cons_succ, Pi.zero_apply]
    · refine Finset.sum_congr rfl fun i _ => ?_
      refine congrArg (fun φ => operatorK1Map φ y) (NonUnitalStarAlgHom.ext fun f => ?_)
      funext j
      change (Pi.single i.succ (f i.succ) : Fin (n + 1) → ℂ) j =
        (Fin.cons (0 : ℂ) (Pi.single i (f i.succ) : Fin n → ℂ) : Fin (n + 1) → ℂ) j
      refine Fin.cases ?_ (fun k => ?_) j
      · rw [Pi.single_eq_of_ne (Fin.succ_ne_zero i).symm, Fin.cons_zero]
      · rw [Fin.cons_succ]
        rcases eq_or_ne k i with rfl | h
        · rw [Pi.single_eq_same, Pi.single_eq_same]
        · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne ((Fin.succ_injective _).ne h)]

variable (ι : Type) [Fintype ι] [DecidableEq ι]

/-- `∑_i (single_i)_* (eval_i)_* y = y` on `K₁(ℂ^ι)`. -/
theorem sum_piSingle_piEval_k1 (y : OperatorK1 (ι → ℂ)) :
    ∑ i, operatorK1Map (piSingleHom ι i) (operatorK1Map (piEvalHom ι i) y) = y := by
  let e := Fintype.equivFin ι
  let σ := piCongrScalarEquiv ι e
  have h := congrArg (operatorK1Map σ.symm.toNonUnitalStarAlgHom)
    (sum_piSingle_piEval_fin_k1 (Fintype.card ι) (operatorK1Map σ.toNonUnitalStarAlgHom y))
  rw [operatorK1_eq_of_starAlgEquiv, map_sum] at h
  conv_rhs => rw [← h]
  simp only [operatorK1Map_apply_apply]
  refine (Fintype.sum_equiv e _ _ fun i => ?_)
  refine congrArg (fun φ => operatorK1Map φ y) (NonUnitalStarAlgHom.ext fun f => ?_)
  funext j
  simp only [NonUnitalStarAlgHom.coe_comp, Function.comp_apply, piEvalHom_apply,
    piSingleHom_apply]
  change (Pi.single i (f i) : ι → ℂ) j =
    (Pi.single (e i) (f (e.symm (e i))) : Fin (Fintype.card ι) → ℂ) (e j)
  rw [Equiv.symm_apply_apply]
  rcases eq_or_ne j i with rfl | hji
  · simp
  · rw [Pi.single_eq_of_ne hji, Pi.single_eq_of_ne (e.injective.ne hji)]

/-- `(eval_j)_* ∑_i (single_i)_* v_i = v_j` on `K₁`. -/
theorem piEval_sum_piSingle_k1 (v : ι → OperatorK1 ℂ) (j : ι) :
    operatorK1Map (piEvalHom ι j) (∑ i, operatorK1Map (piSingleHom ι i) (v i)) = v j := by
  rw [map_sum, Finset.sum_eq_single j]
  · rw [operatorK1Map_apply_apply, piEvalHom_comp_piSingleHom_self, operatorK1Map_id]
    rfl
  · intro _ _ hij
    rw [operatorK1Map_apply_apply, piEvalHom_comp_piSingleHom_of_ne ι hij, operatorK1Map_zero]
    rfl
  · intro h
    exact absurd (Finset.mem_univ j) h

/-- `K₁(ℂ^ι) ≃+ K₁(ℂ)^ι`. -/
def piOperatorK1Equiv : OperatorK1 (ι → ℂ) ≃+ (ι → OperatorK1 ℂ) where
  toFun y i := operatorK1Map (piEvalHom ι i) y
  invFun v := ∑ i, operatorK1Map (piSingleHom ι i) (v i)
  left_inv y := sum_piSingle_piEval_k1 ι y
  right_inv v := funext fun j => piEval_sum_piSingle_k1 ι v j
  map_add' y z := funext fun _ => map_add _ y z

theorem piOperatorK1Equiv_symm_apply (v : ι → OperatorK1 ℂ) :
    (piOperatorK1Equiv ι).symm v = ∑ i, operatorK1Map (piSingleHom ι i) (v i) := rfl

end K1

end BC4lean.OperatorKTheory

namespace BC4lean

open KKTheory CharacterDual

section GroupAlgebra

variable {Γ : Type} [CommGroup Γ] [Fintype Γ]

/-- `g ↦ (ψ ↦ conj ψ(g))`. -/
def characterEvalHom : Γ →* (CharacterDual Γ → ℂ) where
  toFun g ψ := star ((toUnitary ψ g : unitary ℂ) : ℂ)
  map_one' := by
    funext ψ
    simp
  map_mul' g h := by
    funext ψ
    rw [Pi.mul_apply, unitaryChar_mul, star_mul', mul_comm]

@[simp] theorem characterEvalHom_apply (g : Γ) (ψ : CharacterDual Γ) :
    characterEvalHom g ψ = star ((toUnitary ψ g : unitary ℂ) : ℂ) := rfl

/-- The group algebra evaluated at all characters (conjugated): `δ_g ↦ (ψ ↦ conj ψ(g))`. -/
def characterEval : GroupAlgebra Γ →⋆ₐ[ℂ] (CharacterDual Γ → ℂ) where
  toAlgHom := MonoidAlgebra.lift ℂ (CharacterDual Γ → ℂ) Γ characterEvalHom
  map_star' a := by
    induction a using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb =>
      simp only [AlgHom.toFun_eq_coe, star_add, map_add] at ha hb ⊢
      rw [ha, hb]
    | single g z =>
      change MonoidAlgebra.lift ℂ (CharacterDual Γ → ℂ) Γ characterEvalHom
        (GroupAlgebra.involution _) = _
      rw [GroupAlgebra.involution_single]
      funext ψ
      simp only [AlgHom.toFun_eq_coe, MonoidAlgebra.lift_single, Pi.smul_apply, Pi.star_apply,
        smul_eq_mul, characterEvalHom_apply, star_mul', unitaryChar_star]

theorem characterEval_delta (g : Γ) :
    characterEval (GroupAlgebra.delta g) = fun ψ : CharacterDual Γ =>
      star ((toUnitary ψ g : unitary ℂ) : ℂ) := by
  funext ψ
  change MonoidAlgebra.lift ℂ (CharacterDual Γ → ℂ) Γ characterEvalHom
    (MonoidAlgebra.single g 1) ψ = _
  rw [MonoidAlgebra.lift_single, one_smul, characterEvalHom_apply]

variable (Γ) in
/-- The character projection `|Γ|⁻¹ ∑_g χ(g) δ_g` in the group algebra. -/
def groupAlgebraCharProjection (χ : CharacterDual Γ) : GroupAlgebra Γ :=
  ∑ g : Γ, ((Fintype.card Γ : ℂ)⁻¹ * ((toUnitary χ g : unitary ℂ) : ℂ)) • GroupAlgebra.delta g

/-- The character projection goes to the coordinate idempotent. -/
theorem characterEval_charProjection (χ : CharacterDual Γ) :
    characterEval (groupAlgebraCharProjection Γ χ) = Pi.single χ 1 := by
  funext ψ
  rw [groupAlgebraCharProjection, map_sum, Finset.sum_apply]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, characterEval_delta]
  rw [Pi.single_apply, ← CharacterDual.orthogonality ψ χ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun g _ => by ring

theorem characterEval_surjective : Function.Surjective (characterEval (Γ := Γ)) := by
  intro f
  refine ⟨∑ χ, f χ • groupAlgebraCharProjection Γ χ, ?_⟩
  rw [map_sum]
  simp only [map_smul, characterEval_charProjection]
  conv_rhs => rw [← Finset.univ_sum_single f]
  refine Finset.sum_congr rfl fun χ _ => ?_
  rw [← Pi.single_smul', smul_eq_mul, mul_one]

theorem characterEval_injective : Function.Injective (characterEval (Γ := Γ)) := by
  have hrank : Module.finrank ℂ (GroupAlgebra Γ) = Module.finrank ℂ (CharacterDual Γ → ℂ) := by
    rw [Module.finrank_eq_card_basis (MonoidAlgebra.basis Γ ℂ),
      Module.finrank_fintype_fun_eq_card, CharacterDual.card_eq]
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (characterEval (Γ := Γ)).toAlgHom.toLinearMap) hrank).2 characterEval_surjective

variable (Γ) in
/-- The group algebra of a finite abelian group is `ℂ^Γ̂`, by its characters. -/
def finiteAbelianGroupAlgebraEquiv : GroupAlgebra Γ ≃⋆ₐ[ℂ] (CharacterDual Γ → ℂ) :=
  StarAlgEquiv.ofBijective characterEval ⟨characterEval_injective, characterEval_surjective⟩

variable (Γ) in
/-- For a finite abelian group, `f ↦ ∑_χ f(χ) P_χ` is a ⋆-isomorphism `ℂ^Γ̂ ≃ C*_r(Γ)`. -/
def finiteAbelianReducedEquiv : (CharacterDual Γ → ℂ) ≃⋆ₐ[ℂ] ReducedGroupCStar Γ :=
  (finiteAbelianGroupAlgebraEquiv Γ).symm.trans finiteReducedEquiv

/-- The coordinate idempotent at `χ` goes to the character projection. -/
theorem finiteAbelianReducedEquiv_single (χ : CharacterDual Γ) :
    finiteAbelianReducedEquiv Γ (Pi.single χ 1) =
      ∑ g : Γ, ((Fintype.card Γ : ℂ)⁻¹ * ((toUnitary χ g : unitary ℂ) : ℂ)) •
        (⟨regularOperator g, regularOperator_mem_reducedAlgebra g⟩ : ReducedGroupCStar Γ) := by
  have h : (finiteAbelianGroupAlgebraEquiv Γ).symm (Pi.single χ 1) =
      groupAlgebraCharProjection Γ χ := by
    rw [StarAlgEquiv.symm_apply_eq]
    exact (characterEval_charProjection χ).symm
  rw [finiteAbelianReducedEquiv, StarAlgEquiv.trans_apply, h, groupAlgebraCharProjection,
    map_sum]
  simp only [map_smul, finiteReducedEquiv_delta]

end GroupAlgebra

end BC4lean
