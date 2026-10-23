module

/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

public import Note_9_5B_mJet

@[expose] public section

open Complex
open RH95C RH95U RH94 RH113 RHM

namespace RHFinalM

theorem RH_general_unconditional (C : ℝ) (hC : 0 < C)
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
    {σ t : ℝ} (hz : f (↑σ + Complex.I * ↑t) = 0) :
    σ = 1 / 2 ∨ t = 0 := by
  by_cases hσ : σ = 1 / 2
  · exact Or.inl hσ
  · exact Or.inr
      (theorem_10_unconditional C hC E f hE_pos hE_neg hf h_sym h_conj hne σ t hz hσ)

theorem RH_xi_unconditional (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (g : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, g (↑σ + Complex.I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m g (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg : Differentiable ℂ g)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    {s : ℂ} (hz : g s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s.re = 1 / 2 := by

  have hg_ne : ∃ s, g s ≠ 0 := by
    refine ⟨2, ?_⟩
    rw [hg_eq 2 (by norm_num) (by norm_num)]
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by simp]
    obtain ⟨hpos, -⟩ := RH113.lemma_11_3 hζ (x := 2) (by norm_num) (by norm_num)
    intro h
    rw [h] at hpos
    simp at hpos
  by_cases hre : s.re = 1 / 2
  · exact hre
  · exfalso
    by_cases him : s.im = 0
    ·
      have hs : s = (s.re : ℂ) := by
        have h := Complex.re_add_im s
        rw [him] at h
        simp at h
        exact h.symm
      have hx0 : s.re ≠ 0 := by
        intro h
        apply hs0
        rw [hs, h]
        simp
      have hx1 : s.re ≠ 1 := by
        intro h
        apply hs1
        rw [hs, h]
        simp
      rw [hs, hg_eq _ (by exact_mod_cast hx0) (by exact_mod_cast hx1)] at hz
      exact xiFn_ne_zero_ofReal hζ hx0 hx1 hz
    ·

      have hz' : g (↑s.re + Complex.I * ↑s.im) = 0 := by
        rw [mul_comm, Complex.re_add_im]
        exact hz
      have h10 := theorem_10_unconditional C hC E g hE_pos hE_neg hg hg_sym hg_conj
        hg_ne s.re s.im hz' hre
      exact him h10

theorem RH_xi_zeros_unconditional (C : ℝ) (hC : 0 < C)
    (E : ℕ → (Fin 4 → ℂ) → ℝ)
    (g : ℂ → ℂ)
    (hE_pos : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) →
      (∃ σ t : ℝ, g (↑σ + Complex.I * ↑t) = 0 ∧ σ ≠ 1 / 2 ∧ t ≠ 0 ∧
        ∀ i, J i = iteratedDeriv m g (orbitC σ t i)) →
      0 ≤ E m J)
    (hE_neg : ∀ (m : ℕ) (J : Fin 4 → ℂ),
      (∀ i, J (iA i) = (-1) ^ m * star (J i)) →
      (∀ i, J (iB i) = star (J i)) →
      (∀ i, J i ≠ 0) → E m J < 0)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg : Differentiable ℂ g)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    {s : ℂ} (hz : g s = 0) :
    s.re = 1 / 2 ∨ s = 0 ∨ s = 1 := by
  by_cases hs0 : s = 0
  · exact Or.inr (Or.inl hs0)
  · by_cases hs1 : s = 1
    · exact Or.inr (Or.inr hs1)
    · exact Or.inl
        (RH_xi_unconditional C hC E g hE_pos hE_neg hζ hg hg_eq hg_sym hg_conj hz hs0 hs1)

end RHFinalM

section Audit
#print axioms RHFinalM.RH_general_unconditional
#print axioms RHFinalM.RH_xi_unconditional
#print axioms RHFinalM.RH_xi_zeros_unconditional
end Audit

end
