import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Algebra.EuclideanDomain.Basic
import Mathlib.Tactic.LinearCombination

/-!
# `SL_n = E_n` over a Euclidean domain

Over a Euclidean domain `R`, every square matrix of determinant `1` is a product of elementary
transvections `1 + c • E_ij` (`i ≠ j`), and every matrix with unit determinant is such a product
times `diagonal (update 1 i₀ (det M))`.

This is a statement about matrices over a Euclidean domain and does not depend on anything in
BC4lean: it imports Mathlib only and is written in Mathlib's style, with Mathlib's
`TransvectionStruct`. `IsElem` (a product of transvections) is the local name for membership in the
elementary subgroup. The pinned Mathlib proves the analogous statements over a field only
(`Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal`,
`Matrix.SpecialLinearGroup.diagonal_transvection_induction`); this file does not use them.

Proof. Row transvections run the Euclidean algorithm on the last column (`exists_isElem_mulVec_eq_single`):
the column becomes `d • e_k`. Invertibility makes `d` a unit (`isUnit_of_col_eq_single`), and two
more transvections turn `d • e_k` into `e_last`. The matrix is then
`fromBlocks A 0 0 1 * fromBlocks 1 0 x 1`; the second factor is a product of transvections
(`isElem_fromBlocks_one_zero_one`) and `det A = 1`, so induction on the size finishes.
-/

namespace BC4lean.EuclideanSL

open Matrix

variable {R : Type*} [EuclideanDomain R]

section General

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- `M` is a product of elementary transvections (the elementary group `E_n(R)`). -/
def IsElem (M : Matrix n n R) : Prop :=
  ∃ L : List (TransvectionStruct n R), (L.map TransvectionStruct.toMatrix).prod = M

theorem isElem_one : IsElem (1 : Matrix n n R) := ⟨[], by simp⟩

theorem IsElem.mul {M N : Matrix n n R} (hM : IsElem M) (hN : IsElem N) : IsElem (M * N) := by
  obtain ⟨L, rfl⟩ := hM
  obtain ⟨L', rfl⟩ := hN
  exact ⟨L ++ L', by simp⟩

theorem isElem_transvection {i j : n} (h : i ≠ j) (c : R) : IsElem (transvection i j c) :=
  ⟨[⟨i, j, h, c⟩], by simp⟩

theorem IsElem.det {M : Matrix n n R} (hM : IsElem M) : M.det = 1 := by
  obtain ⟨L, rfl⟩ := hM
  exact TransvectionStruct.det_toMatrix_prod L

/-- Elementary matrices have elementary left inverses. -/
theorem IsElem.exists_inv {M : Matrix n n R} (hM : IsElem M) : ∃ M', IsElem M' ∧ M' * M = 1 := by
  obtain ⟨L, rfl⟩ := hM
  exact ⟨_, ⟨L.reverse.map TransvectionStruct.inv, by rw [List.map_map]⟩,
    TransvectionStruct.reverse_inv_prod_mul_prod L⟩

theorem IsElem.reindex {p : Type*} [Fintype p] [DecidableEq p] (e : n ≃ p) {M : Matrix n n R}
    (hM : IsElem M) : IsElem (Matrix.reindex e e M) := by
  obtain ⟨L, rfl⟩ := hM
  exact ⟨L.map (TransvectionStruct.reindexEquiv e), by
    rw [List.map_map, TransvectionStruct.toMatrix_reindexEquiv_prod, coe_reindexAlgEquiv]⟩

theorem IsElem.fromBlocks_one {p : Type*} [Fintype p] [DecidableEq p] {M : Matrix n n R}
    (hM : IsElem M) : IsElem (fromBlocks M 0 0 (1 : Matrix p p R)) := by
  obtain ⟨L, rfl⟩ := hM
  refine ⟨L.map (TransvectionStruct.sumInl p), ?_⟩
  have h := TransvectionStruct.sumInl_toMatrix_prod_mul (p := p) (1 : Matrix n n R) L (1 : Matrix p p R)
  rw [Matrix.fromBlocks_one, Matrix.mul_one, Matrix.mul_one] at h
  rw [List.map_map]
  exact h

theorem transvection_mulVec (i j : n) (c : R) (v : n → R) :
    transvection i j c *ᵥ v = Function.update v i (v i + c * v j) := by
  ext x
  simp only [transvection, add_mulVec, one_mulVec, single_mulVec, Pi.add_apply]
  by_cases hx : x = i
  · subst hx; simp
  · simp [hx]

open Classical in
/-- One step of the Euclidean algorithm, by strong induction on the pivot `a` (for the Euclidean
relation) and then on the number of other nonzero entries. -/
theorem exists_isElem_mulVec_eq_single_aux (a : R) :
    ∀ (m : ℕ) (v : n → R) (k : n), v k = a → a ≠ 0 →
      (Finset.univ.filter fun i => i ≠ k ∧ v i ≠ 0).card ≤ m →
      ∃ P : Matrix n n R, IsElem P ∧ ∃ k' d, P *ᵥ v = Pi.single k' d := by
  induction a using (EuclideanDomain.r_wellFounded (R := R)).induction with
  | _ a IHa =>
  intro m
  induction m with
  | zero =>
    intro v k hk _ hm
    refine ⟨1, isElem_one, k, a, ?_⟩
    rw [one_mulVec]
    ext i
    by_cases hi : i = k
    · subst hi; simp [hk]
    · rw [Pi.single_eq_of_ne hi]
      by_contra hvi
      have hmem : i ∈ Finset.univ.filter fun i => i ≠ k ∧ v i ≠ 0 := by simp [hi, hvi]
      have := Finset.card_pos.mpr ⟨i, hmem⟩
      omega
  | succ m IHm =>
    intro v k hk ha hm
    by_cases hall : ∀ i, i ≠ k → v i = 0
    · refine ⟨1, isElem_one, k, a, ?_⟩
      rw [one_mulVec]
      ext i
      by_cases hi : i = k
      · subst hi; simp [hk]
      · rw [Pi.single_eq_of_ne hi, hall i hi]
    push Not at hall
    obtain ⟨i, hik, hvi⟩ := hall
    set w := Function.update v i (v i % a) with hw
    have hTw : transvection i k (-(v i / a)) *ᵥ v = w := by
      rw [transvection_mulVec, hw, hk]
      congr 1
      linear_combination -(EuclideanDomain.div_add_mod (v i) a)
    have hwk : w k = a := by simp [hw, hik.symm, hk]
    have hT := isElem_transvection hik (-(v i / a))
    by_cases hr : v i % a = 0
    · have hcard : (Finset.univ.filter fun j => j ≠ k ∧ w j ≠ 0).card ≤ m := by
        have hsub : (Finset.univ.filter fun j => j ≠ k ∧ w j ≠ 0) ⊂
            (Finset.univ.filter fun j => j ≠ k ∧ v j ≠ 0) := by
          rw [Finset.ssubset_iff_of_subset]
          · exact ⟨i, by simp [hik, hvi], by simp [hw, hr]⟩
          · intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
            refine ⟨hj.1, ?_⟩
            by_cases hji : j = i
            · subst hji
              exact absurd (by simp [hw, hr]) hj.2
            · simpa [hw, Function.update_apply, hji] using hj.2
        have := Finset.card_lt_card hsub
        omega
      obtain ⟨P, hP, k', d, hPd⟩ := IHm w k hwk ha hcard
      exact ⟨P * transvection i k (-(v i / a)), hP.mul hT, k', d, by
        rw [← mulVec_mulVec, hTw, hPd]⟩
    · obtain ⟨P, hP, k', d, hPd⟩ :=
        IHa _ (EuclideanDomain.mod_lt (v i) ha) _ w i (by simp [hw]) hr le_rfl
      exact ⟨P * transvection i k (-(v i / a)), hP.mul hT, k', d, by
        rw [← mulVec_mulVec, hTw, hPd]⟩

/-- Row transvections bring any nonzero vector to the form `d • e_k`. -/
theorem exists_isElem_mulVec_eq_single (v : n → R) (hv : v ≠ 0) :
    ∃ P : Matrix n n R, IsElem P ∧ ∃ k d, P *ᵥ v = Pi.single k d := by
  obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  exact exists_isElem_mulVec_eq_single_aux (v k) _ v k rfl hk le_rfl

/-- `u • e_k` with `u` a unit goes to `e_l` (`k ≠ l`) by two transvections. -/
theorem exists_isElem_mulVec_single_unit {k l : n} (hkl : k ≠ l) (u : Rˣ) :
    ∃ P : Matrix n n R, IsElem P ∧ P *ᵥ Pi.single k (u : R) = Pi.single l 1 := by
  refine ⟨transvection k l (-(u : R)) * transvection l k (↑u⁻¹ : R),
    (isElem_transvection hkl _).mul (isElem_transvection hkl.symm _), ?_⟩
  rw [← mulVec_mulVec, transvection_mulVec, transvection_mulVec]
  ext x
  by_cases hxk : x = k
  · subst hxk; simp [hkl, hkl.symm]
  · by_cases hxl : x = l
    · subst hxl; simp [hkl, hkl.symm]
    · simp [Function.update_apply, hxk, hxl, Pi.single_apply]

/-- If a column of an invertible matrix is `d • e_k`, then `d` is a unit. -/
theorem isUnit_of_col_eq_single {N : Matrix n n R} (hN : IsUnit N.det) {j k : n} {d : R}
    (hcol : ∀ x, N x j = (Pi.single k d : n → R) x) : IsUnit d := by
  have h := congrFun (congrFun (adjugate_mul N) j) j
  simp only [mul_apply, hcol, Pi.single_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one] at h
  exact IsUnit.of_mul_eq_one (adjugate N j k * hN.unit⁻¹) (by
    rw [mul_comm, mul_assoc, mul_comm _ d, ← mul_assoc, h, IsUnit.mul_val_inv])

/-- `fromBlocks 1 0 x 1` is a product of transvections. -/
theorem isElem_fromBlocks_one_zero_one {p q : Type*} [Fintype p] [DecidableEq p] [Fintype q]
    [DecidableEq q] (x : Matrix q p R) :
    IsElem (fromBlocks (1 : Matrix p p R) 0 x (1 : Matrix q q R)) := by
  let Q : Matrix q p R → Prop := fun x => IsElem (fromBlocks (1 : Matrix p p R) 0 x 1)
  have hadd : ∀ a b, Q a → Q b → Q (a + b) := by
    intro a b ha hb
    have h := ha.mul hb
    rw [fromBlocks_multiply] at h
    simpa using h
  have h0 : Q 0 := by
    show IsElem (fromBlocks (1 : Matrix p p R) 0 0 1)
    rw [fromBlocks_one]
    exact isElem_one
  have hs : ∀ i j c, Q (single i j c) := by
    intro i j c
    have h := isElem_transvection (n := p ⊕ q) (i := Sum.inr i) (j := Sum.inl j) (by simp) c
    convert h using 1
    ext (a | a) (b | b) <;> simp [transvection, single_apply, one_apply]
  rw [matrix_eq_sum_single x]
  exact Finset.sum_induction _ Q hadd h0 fun i _ =>
    Finset.sum_induction _ Q hadd h0 fun j _ => hs i j _

end General

/-- Induction step on `Fin r ⊕ Unit`, the last index as pivot. -/
theorem isElem_step (r : ℕ)
    (IH : ∀ A : Matrix (Fin r) (Fin r) R, A.det = 1 → IsElem A)
    (M : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) R) (hM : M.det = 1) : IsElem M := by
  -- the last column is nonzero
  set v : Fin r ⊕ Unit → R := fun i => M i (Sum.inr ()) with hv
  have hv0 : v ≠ 0 := by
    intro h
    have := det_eq_zero_of_column_eq_zero (Sum.inr ()) (fun i => congrFun h i)
    rw [hM] at this
    exact one_ne_zero this
  obtain ⟨P, hP, k, d, hPv⟩ := exists_isElem_mulVec_eq_single v hv0
  set N := P * M with hN
  have hNdet : N.det = 1 := by rw [hN, det_mul, hP.det, hM, one_mul]
  have hNcol : ∀ x, N x (Sum.inr ()) = (Pi.single k d : Fin r ⊕ Unit → R) x :=
    fun x => congrFun hPv x
  have hd : IsUnit d := isUnit_of_col_eq_single (by rw [hNdet]; exact isUnit_one) hNcol
  -- move `d • e_k` to `e_last`
  obtain ⟨Q, hQ, hQv⟩ : ∃ Q : Matrix (Fin r ⊕ Unit) (Fin r ⊕ Unit) R, IsElem Q ∧
      Q *ᵥ Pi.single k d = Pi.single (Sum.inr ()) 1 := by
    by_cases hk : k = Sum.inr ()
    · cases r with
      | zero =>
        -- `1 × 1`: `d = det N = 1`
        refine ⟨1, isElem_one, ?_⟩
        let _ : Unique (Fin 0 ⊕ Unit) :=
          { default := Sum.inr (), uniq := by rintro (i | ⟨⟩) <;> first | exact i.elim0 | rfl }
        have h1 : d = 1 := by
          rw [det_unique] at hNdet
          have h2 : N (Sum.inr ()) (Sum.inr ()) = d := by rw [hNcol, hk, Pi.single_eq_same]
          rw [← h2]
          exact hNdet
        rw [one_mulVec, hk, h1]
      | succ r =>
        have hne : k ≠ Sum.inl 0 := by rw [hk]; simp
        obtain ⟨Q₁, hQ₁, hQ₁v⟩ := exists_isElem_mulVec_single_unit hne hd.unit
        obtain ⟨Q₂, hQ₂, hQ₂v⟩ := exists_isElem_mulVec_single_unit
          (show (Sum.inl 0 : Fin (r + 1) ⊕ Unit) ≠ Sum.inr () by simp) (1 : Rˣ)
        refine ⟨Q₂ * Q₁, hQ₂.mul hQ₁, ?_⟩
        rw [← mulVec_mulVec, show d = (hd.unit : R) from rfl, hQ₁v]
        simpa using hQ₂v
    · obtain ⟨Q, hQ, hQv⟩ := exists_isElem_mulVec_single_unit hk hd.unit
      exact ⟨Q, hQ, hQv⟩
  set M₁ := Q * N with hM₁
  have hM₁det : M₁.det = 1 := by rw [hM₁, det_mul, hQ.det, hNdet, one_mul]
  have hM₁col : ∀ x, M₁ x (Sum.inr ()) = (Pi.single (Sum.inr ()) 1 : Fin r ⊕ Unit → R) x := by
    intro x
    have : (fun y => N y (Sum.inr ())) = Pi.single k d := funext hNcol
    rw [← hQv, ← this]
    rfl
  -- block decomposition
  set A := toBlocks₁₁ M₁
  set X := toBlocks₂₁ M₁
  have hblk : M₁ = fromBlocks A 0 0 (1 : Matrix Unit Unit R) * fromBlocks 1 0 X 1 := by
    rw [fromBlocks_multiply]
    simp only [Matrix.mul_one, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
      Matrix.one_mul]
    ext (a | ⟨⟩) (b | ⟨⟩)
    · rfl
    · simpa using hM₁col (Sum.inl a)
    · rfl
    · simpa using hM₁col (Sum.inr ())
  have hA : A.det = 1 := by
    have h := hM₁det
    rw [hblk, det_mul, (isElem_fromBlocks_one_zero_one X).det, mul_one, det_fromBlocks_zero₂₁,
      det_one, mul_one] at h
    exact h
  have hM₁elem : IsElem M₁ := by
    rw [hblk]
    exact (IH A hA).fromBlocks_one.mul (isElem_fromBlocks_one_zero_one X)
  obtain ⟨P', hP', hP'P⟩ := hP.exists_inv
  obtain ⟨Q', hQ', hQ'Q⟩ := hQ.exists_inv
  have hMeq : M = P' * (Q' * M₁) := by
    rw [hM₁, ← Matrix.mul_assoc Q', hQ'Q, Matrix.one_mul, hN, ← Matrix.mul_assoc, hP'P,
      Matrix.one_mul]
  rw [hMeq]
  exact hP'.mul (hQ'.mul hM₁elem)

theorem isElem_of_det_eq_one_aux (r : ℕ) :
    ∀ (n : Type) [Fintype n] [DecidableEq n], Fintype.card n = r →
      ∀ M : Matrix n n R, M.det = 1 → IsElem M := by
  induction r with
  | zero =>
    intro n _ _ hn M _
    have : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    rw [Subsingleton.elim M 1]
    exact isElem_one
  | succ r IH =>
    intro n _ _ hn M hM
    let e : n ≃ Fin r ⊕ Unit := Fintype.equivOfCardEq (by simp [hn])
    have h := isElem_step r (fun A hA => IH (Fin r) (by simp) A hA) (Matrix.reindex e e M)
      (by rw [det_reindex_self, hM])
    simpa using h.reindex e.symm

/-- **`SL_n = E_n` over a Euclidean domain.** A square matrix of determinant `1` is a product of
elementary transvections. -/
theorem exists_list_transvec_eq_of_det_eq_one {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n R) (hM : M.det = 1) :
    ∃ L : List (TransvectionStruct n R), (L.map TransvectionStruct.toMatrix).prod = M := by
  let e := Fintype.equivFin n
  have h := isElem_of_det_eq_one_aux (Fintype.card n) (Fin (Fintype.card n)) (by simp)
    (Matrix.reindex e e M) (by rw [det_reindex_self, hM])
  have h' : IsElem M := by simpa using h.reindex e.symm
  exact h'

/-- **`GL_n = E_n · diag` over a Euclidean domain.** A matrix with unit determinant is a product of
transvections times `diagonal (update 1 i₀ (det M))`. -/
theorem exists_list_transvec_mul_diagonal_eq {n : Type*} [Fintype n] [DecidableEq n] (i₀ : n)
    (M : Matrix n n R) (hM : IsUnit M.det) :
    ∃ L : List (TransvectionStruct n R),
      (L.map TransvectionStruct.toMatrix).prod * diagonal (Function.update 1 i₀ M.det) = M := by
  set D' : Matrix n n R := diagonal (Function.update 1 i₀ (↑hM.unit⁻¹ : R))
  have hD : D' * diagonal (Function.update 1 i₀ M.det) = 1 := by
    rw [diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext x
    by_cases hx : x = i₀
    · subst hx; simp
    · simp [hx]
  have hdet : (M * D').det = 1 := by
    rw [det_mul, det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ _)]
    simp
  obtain ⟨L, hL⟩ := exists_list_transvec_eq_of_det_eq_one (M * D') hdet
  exact ⟨L, by rw [hL, Matrix.mul_assoc, hD, Matrix.mul_one]⟩

end BC4lean.EuclideanSL
