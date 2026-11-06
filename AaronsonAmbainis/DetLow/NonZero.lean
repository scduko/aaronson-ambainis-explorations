import AaronsonAmbainis.DetLow.Basic

/-!
# DetLow: the determinant of the agreement matrix is nonzero

This is Lemma 3.4 of the paper. Specialize every variable to a single indeterminate.
The identity permutation contributes the unique term of maximal degree, with coefficient one.
-/

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Specialization of every variable to the same univariate polynomial. -/
noncomputable def specialize (c : Polynomial ℤ) : MvPolynomial ι ℤ →+* Polynomial ℤ :=
  eval₂Hom Polynomial.C (fun _ => c)

/-- The number of coordinates in which `x` and `z` agree. -/
def agCount (x z : Cube ι) : ℕ := (univ.filter fun i => x i = z i).card

omit [DecidableEq ι] in
theorem specialize_agMon (c : Polynomial ℤ) (x z : Cube ι) :
    specialize c (agMon x z) = c ^ agCount x z := by
  have h : ∀ i, specialize c (if x i = z i then (X i : MvPolynomial ι ℤ) else 1)
      = if x i = z i then c else 1 := by
    intro i
    by_cases hi : x i = z i
    · rw [if_pos hi, if_pos hi]
      simp [specialize]
    · rw [if_neg hi, if_neg hi, map_one]
  unfold agMon agCount
  rw [map_prod]
  simp_rw [h]
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]

omit [DecidableEq ι] in
theorem agCount_self (x : Cube ι) : agCount x x = Fintype.card ι := by
  simp [agCount]

omit [DecidableEq ι] in
theorem agCount_lt (x z : Cube ι) (h : x ≠ z) : agCount x z < Fintype.card ι := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  unfold agCount
  rw [← Finset.card_univ]
  apply Finset.card_lt_card
  rw [Finset.filter_ssubset]
  exact ⟨i, mem_univ i, hi⟩

omit [DecidableEq ι] in
theorem agCount_le (x z : Cube ι) : agCount x z ≤ Fintype.card ι := by
  simpa [agCount] using (Finset.card_filter_le (s := (univ : Finset ι))
    (p := fun i => x i = z i))

/-- Only the identity permutation attains the maximal sum of agreement counts. -/
theorem agreement_sum_lt (g : Cube ι → Bool) (σ : Equiv.Perm (Ones g)) (hσ : σ ≠ 1) :
    ∑ x, agCount (σ x).1 x.1 < Fintype.card (Ones g) * Fintype.card ι := by
  classical
  have hex : ∃ x, σ x ≠ x := by
    by_contra! h
    exact hσ (Equiv.ext h)
  obtain ⟨x, hx⟩ := hex
  calc
    ∑ x, agCount (σ x).1 x.1 < ∑ _x : Ones g, Fintype.card ι := by
      apply Finset.sum_lt_sum
      · intro y _
        exact agCount_le _ _
      · exact ⟨x, mem_univ x, agCount_lt _ _ (fun h => hx (Subtype.ext h))⟩
    _ = _ := by simp

/-- The top coefficient after specialization is one. -/
theorem specialized_det_coeff (g : Cube ι → Bool) :
    (((specialize Polynomial.X).mapMatrix (agMatrix g)).det).coeff
      (Fintype.card (Ones g) * Fintype.card ι) = 1 := by
  classical
  have hterm (σ : Equiv.Perm (Ones g)) :
      (∏ x, (specialize Polynomial.X).mapMatrix (agMatrix g) (σ x) x) =
        (Polynomial.X : Polynomial ℤ) ^ (∑ x, agCount (σ x).1 x.1) := by
    change (∏ x, specialize Polynomial.X (agMon (σ x).1 x.1)) = _
    simp_rw [specialize_agMon]
    exact Finset.prod_pow_eq_pow_sum _ _ _
  rw [Matrix.det_apply]
  simp_rw [hterm]
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Ones g))]
  · simp [agCount_self]
  · intro σ _ hσ
    have hlt := agreement_sum_lt g σ hσ
    simp [Polynomial.coeff_X_pow, Nat.ne_of_gt hlt]
  · simp

/-- Lemma 3.4 of the paper: the determinant of the agreement matrix is nonzero. -/
theorem agMatrix_det_ne_zero (g : Cube ι → Bool) : (agMatrix g).det ≠ 0 := by
  intro h0
  have h := specialized_det_coeff g
  rw [← RingHom.map_det, h0, map_zero] at h
  simp at h

end DetLow
end AaronsonAmbainis
