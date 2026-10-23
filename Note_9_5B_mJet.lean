module

/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

public import Theorem_9_5_Closure
public import Lemma_11_3

@[expose] public section

open RH95C RH95U RH94 RH113 Complex Filter Topology
open scoped ComplexConjugate

namespace RHM

theorem exists_iteratedDeriv_ne_zero {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (ρ : ℂ) : ∃ m : ℕ, iteratedDeriv m f ρ ≠ 0 := by
  by_contra h
  push_neg at h
  rcases hf.analyticAt ρ with ⟨p, r, hpb⟩

  have hp0 : p = 0 := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro v
    show p n v = 0
    have hsum := hpb.iteratedFDeriv_eq_sum_of_completeSpace (fun _ : Fin n => (1 : ℂ))
    have hderiv : iteratedFDeriv ℂ n f ρ (fun _ => 1) = 0 := h n
    rw [hderiv] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hsum
    have hp1 : p n (fun _ => 1) = 0 := by
      rcases smul_eq_zero.mp hsum.symm with h1 | h1
      · exact absurd h1 (Nat.factorial_ne_zero n)
      · exact h1
    calc p n v = p n (fun i => v i • (1 : ℂ)) := by congr 1; funext i; simp
      _ = (∏ i, v i) • p n (fun _ => 1) :=
          ContinuousMultilinearMap.map_smul_univ (p n) v (fun _ => 1)
      _ = 0 := by rw [hp1, smul_zero]

  have hpA : HasFPowerSeriesAt f p ρ := ⟨r, hpb⟩
  have hev : f =ᶠ[𝓝 ρ] 0 := hpA.locally_zero_iff.mpr hp0
  have hfA : AnalyticOnNhd ℂ f Set.univ := fun x _ => hf.analyticAt x
  have h0 : Set.EqOn f 0 Set.univ :=
    hfA.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_univ
      (Set.mem_univ ρ) hev
  rcases hne with ⟨s, hs⟩
  exact hs (h0 (Set.mem_univ s))

noncomputable def jetOrder {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (z : ℂ) : ℕ :=
  Nat.find (exists_iteratedDeriv_ne_zero hf hne z)

lemma jetOrder_spec {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (z : ℂ) :
    iteratedDeriv (jetOrder hf hne z) f z ≠ 0 :=
  Nat.find_spec (exists_iteratedDeriv_ne_zero hf hne z)

theorem iteratedDeriv_reflA {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (m : ℕ) (z : ℂ) :
    iteratedDeriv m f (1 - z) = (-1) ^ m * iteratedDeriv m f z := by
  have hgs : (fun s => f (1 - s)) = f := funext h_sym
  have hkey : ∀ m : ℕ, ∀ z : ℂ,
      iteratedDeriv m (fun s => f (1 - s)) z = (-1) ^ m * iteratedDeriv m f (1 - z) := by
    intro m
    induction m with
    | zero => intro z; simp [iteratedDeriv_zero]
    | succ m ih =>
      intro z
      have hd : Differentiable ℂ (iteratedDeriv m f) :=
        ContDiff.differentiable_iteratedDeriv' m (hf.contDiff)
      have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) z := by
        simpa using (hasDerivAt_id z).const_sub (1 : ℂ)
      have hcomp : HasDerivAt (fun w => iteratedDeriv m f (1 - w))
          (deriv (iteratedDeriv m f) (1 - z) * (-1)) z :=
        (hd (1 - z)).hasDerivAt.comp z hsub
      have hd2 : DifferentiableAt ℂ (fun w => iteratedDeriv m f (1 - w)) z :=
        (hd.comp ((differentiable_const (1 : ℂ)).sub differentiable_id)).differentiableAt
      rw [iteratedDeriv_succ]
      have hfun : ∀ w, iteratedDeriv m (fun s => f (1 - s)) w =
          (-1) ^ m * iteratedDeriv m f (1 - w) := ih
      have hev : (fun w => iteratedDeriv m (fun s => f (1 - s)) w) =ᶠ[𝓝 z]
          (fun w => (-1:ℂ) ^ m * iteratedDeriv m f (1 - w)) :=
        Filter.Eventually.of_forall hfun
      have hderiv_eq : deriv (iteratedDeriv m (fun s => f (1 - s))) z =
          deriv (fun w => (-1) ^ m * iteratedDeriv m f (1 - w)) z := hev.deriv_eq
      rw [hderiv_eq, deriv_const_mul _ hd2, hcomp.deriv, ← iteratedDeriv_succ]
      ring
  have e := hkey m z
  rw [hgs] at e
  have hc : (-1 : ℂ) ^ m * (-1) ^ m = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  calc iteratedDeriv m f (1 - z)
      = ((-1 : ℂ) ^ m * (-1) ^ m) * iteratedDeriv m f (1 - z) := by rw [hc]; simp
    _ = (-1 : ℂ) ^ m * ((-1) ^ m * iteratedDeriv m f (1 - z)) := by ring
    _ = (-1 : ℂ) ^ m * iteratedDeriv m f z := by rw [← e]

theorem iteratedDeriv_reflB {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (h_conj : ∀ s, f (star s) = star (f s)) (m : ℕ) (z : ℂ) :
    iteratedDeriv m f (star z) = star (iteratedDeriv m f z) := by
  have hgs : (fun s => star (f (star s))) = f := by
    funext s
    rw [h_conj s]
    simp
  have hkey : ∀ m : ℕ, ∀ z : ℂ,
      iteratedDeriv m (fun s => star (f (star s))) z = star (iteratedDeriv m f (star z)) := by
    intro m
    induction m with
    | zero => intro z; simp [iteratedDeriv_zero]
    | succ m ih =>
      intro z
      have hd : Differentiable ℂ (iteratedDeriv m f) :=
        ContDiff.differentiable_iteratedDeriv' m (hf.contDiff)
      rw [iteratedDeriv_succ]
      have hfun : ∀ w, iteratedDeriv m (fun s => star (f (star s))) w =
          star (iteratedDeriv m f (star w)) := ih
      have hev : (fun w => iteratedDeriv m (fun s => star (f (star s))) w) =ᶠ[𝓝 z]
          (fun w => star (iteratedDeriv m f (star w))) :=
        Filter.Eventually.of_forall hfun
      have hderiv_eq : deriv (iteratedDeriv m (fun s => star (f (star s)))) z =
          deriv (fun w => star (iteratedDeriv m f (star w))) z := hev.deriv_eq

      have hder : deriv (fun w => star (iteratedDeriv m f (star w))) z =
          star (deriv (iteratedDeriv m f) (star z)) := by
        have h : HasDerivAt (star ∘ iteratedDeriv m f ∘ conj)
            (star (deriv (iteratedDeriv m f) (star z))) z := by
          rw [hasDerivAt_star_conj_iff, star_star]
          exact (hd (star z)).hasDerivAt
        exact h.deriv
      rw [hderiv_eq, hder]
      have e : iteratedDeriv (m + 1) f (star z) = deriv (iteratedDeriv m f) (star z) := by
        rw [iteratedDeriv_succ]
      rw [e]
  have e := hkey m z
  rw [hgs] at e
  rw [e, star_star]

lemma jetOrder_star_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (h_conj : ∀ s, f (star s) = star (f s)) (z : ℂ) :
    jetOrder hf hne (star z) ≤ jetOrder hf hne z := by
  apply Nat.find_le
  rw [iteratedDeriv_reflB hf h_conj, ne_eq, star_eq_zero]
  exact jetOrder_spec hf hne z

lemma jetOrder_star {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0) (h_conj : ∀ s, f (star s) = star (f s)) (z : ℂ) :
    jetOrder hf hne (star z) = jetOrder hf hne z :=
  le_antisymm (jetOrder_star_le hf hne h_conj z) (by
    have h := jetOrder_star_le hf hne h_conj (star z)
    rwa [star_star] at h)

lemma jetOrder_one_sub_star_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s)) (z : ℂ) :
    jetOrder hf hne (1 - star z) ≤ jetOrder hf hne z := by
  apply Nat.find_le
  rw [iteratedDeriv_reflA hf h_sym, iteratedDeriv_reflB hf h_conj]
  exact mul_ne_zero (pow_ne_zero _ (by norm_num : (-1 : ℂ) ≠ 0)) (by
    rw [ne_eq, star_eq_zero]
    exact jetOrder_spec hf hne z)

lemma jetOrder_one_sub_star {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hne : ∃ s, f s ≠ 0)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s)) (z : ℂ) :
    jetOrder hf hne (1 - star z) = jetOrder hf hne z :=
  le_antisymm (jetOrder_one_sub_star_le hf hne h_sym h_conj z) (by
    have h := jetOrder_one_sub_star_le hf hne h_sym h_conj (1 - star z)
    have h2 : 1 - star (1 - star z) = z := by simp
    rwa [h2] at h)

noncomputable def orbitC (σ t : ℝ) : Fin 4 → ℂ :=
  ![↑σ + Complex.I * ↑t, 1 - star (↑σ + Complex.I * ↑t),
    star (↑σ + Complex.I * ↑t), 1 - (↑σ + Complex.I * ↑t)]

lemma orbitC_iA (σ t : ℝ) : ∀ i, orbitC σ t (iA i) = 1 - star (orbitC σ t i) := by
  intro i
  fin_cases i <;> simp [orbitC, iA]

lemma orbitC_iB (σ t : ℝ) : ∀ i, orbitC σ t (iB i) = star (orbitC σ t i) := by
  intro i
  fin_cases i <;> simp [orbitC, iB]

theorem theorem_9_5_multiplicity (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (f : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hne : ∃ s, f s ≠ 0)
    {σ t : ℝ} (hz : f (↑σ + Complex.I * ↑t) = 0) (hσ : σ ≠ 1/2) (ht : t ≠ 0) :
    False := by

  set m₀ := jetOrder hf hne (orbitC σ t 0) with hm₀
  have hm : ∀ i, jetOrder hf hne (orbitC σ t i) = m₀ := by
    intro i
    fin_cases i
    · rfl
    · show jetOrder hf hne (orbitC σ t (1 : Fin 4)) = m₀
      have e : orbitC σ t 1 = 1 - star (orbitC σ t 0) := orbitC_iA σ t 0
      rw [e]
      exact jetOrder_one_sub_star hf hne h_sym h_conj _
    · show jetOrder hf hne (orbitC σ t (2 : Fin 4)) = m₀
      have e : orbitC σ t 2 = star (orbitC σ t 0) := orbitC_iB σ t 0
      rw [e]
      exact jetOrder_star hf hne h_conj _
    · show jetOrder hf hne (orbitC σ t (3 : Fin 4)) = m₀
      have e : orbitC σ t 3 = 1 - star (orbitC σ t 2) := orbitC_iA σ t 2
      rw [e, jetOrder_one_sub_star hf hne h_sym h_conj]
      have e2 : orbitC σ t 2 = star (orbitC σ t 0) := orbitC_iB σ t 0
      rw [e2]
      exact jetOrder_star hf hne h_conj _

  set J : Fin 4 → ℂ := fun i => iteratedDeriv m₀ f (orbitC σ t i) with hJ_def
  have hJ : ∀ i, J i ≠ 0 := by
    intro i
    rw [hJ_def]
    show iteratedDeriv m₀ f (orbitC σ t i) ≠ 0
    rw [← hm i]
    exact jetOrder_spec hf hne _

  have hpairA : ∀ i, J (iA i) = (-1) ^ m₀ * star (J i) := by
    intro i
    show iteratedDeriv m₀ f (orbitC σ t (iA i)) =
      (-1) ^ m₀ * star (iteratedDeriv m₀ f (orbitC σ t i))
    rw [orbitC_iA, iteratedDeriv_reflA hf h_sym, iteratedDeriv_reflB hf h_conj]
  have hpairB : ∀ i, J (iB i) = star (J i) := by
    intro i
    show iteratedDeriv m₀ f (orbitC σ t (iB i)) =
      star (iteratedDeriv m₀ f (orbitC σ t i))
    rw [orbitC_iB, iteratedDeriv_reflB hf h_conj]

  exact absurd (hE_pos m₀ J hpairA hpairB hJ ⟨σ, t, hz, hσ, ht, fun i => congrFun hJ_def i⟩)
    (not_le_of_gt (hE_neg m₀ J hpairA hpairB hJ))

theorem theorem_10_unconditional (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (f : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m f (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hne : ∃ s, f s ≠ 0) :
    ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 → σ ≠ 1/2 → t = 0 := by
  intro σ t hz hσ
  by_contra ht
  exact theorem_9_5_multiplicity C hC E f hE_pos hE_neg hf h_sym h_conj hne hz hσ ht

end RHM

section Audit
#print axioms RHM.exists_iteratedDeriv_ne_zero
#print axioms RHM.iteratedDeriv_reflA
#print axioms RHM.iteratedDeriv_reflB
#print axioms RHM.jetOrder_star
#print axioms RHM.jetOrder_one_sub_star
#print axioms RHM.theorem_9_5_multiplicity
#print axioms RHM.theorem_10_unconditional
end Audit

end
