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

open Complex
open RH95C RH95U RH94 RH95Final RH113

namespace RHFinal

theorem xiFn_differentiableAt {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    DifferentiableAt ℂ xiFn s := by
  unfold xiFn
  exact DifferentiableAt.mul (by fun_prop) (differentiableAt_completedZeta hs0 hs1)

theorem RH_general (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 →
      deriv f (↑σ + Complex.I * ↑t) ≠ 0)
    (hunit : SatisfiesUnitarity C f)
    {σ t : ℝ} (hz : f (↑σ + Complex.I * ↑t) = 0) :
    σ = 1 / 2 ∨ t = 0 := by
  by_cases hσ : σ = 1 / 2
  · exact Or.inl hσ
  · exact Or.inr (theorem_10_final C hC f hf h_sym h_conj hsimple hunit σ t hz hσ)

theorem RH_xi (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hunit : SatisfiesUnitarity C g)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + Complex.I * ↑t) = 0 →
      deriv g (↑σ + Complex.I * ↑t) ≠ 0)
    {s : ℂ} (hz : g s = 0) (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s.re = 1 / 2 := by
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
      have h10 := theorem_10_final C hC g hg hg_sym hg_conj hg_simple hunit s.re s.im hz' hre
      exact him h10

theorem RH_xi_zeros (C : ℝ) (hC : 0 < C)
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hunit : SatisfiesUnitarity C g)
    (hζ : ∀ x : ℝ, 0 < x → x < 1 → (riemannZeta (x : ℂ)).re < 0)
    (hg_eq : ∀ s : ℂ, s ≠ 0 → s ≠ 1 → g s = xiFn s)
    (hg_sym : ∀ s, g (1 - s) = g s) (hg_conj : ∀ s, g (star s) = star (g s))
    (hg_simple : ∀ σ t : ℝ, g (↑σ + Complex.I * ↑t) = 0 →
      deriv g (↑σ + Complex.I * ↑t) ≠ 0)
    {s : ℂ} (hz : g s = 0) :
    s.re = 1 / 2 ∨ s = 0 ∨ s = 1 := by
  by_cases hs0 : s = 0
  · exact Or.inr (Or.inl hs0)
  · by_cases hs1 : s = 1
    · exact Or.inr (Or.inr hs1)
    · exact Or.inl (RH_xi C hC g hg hunit hζ hg_eq hg_sym hg_conj hg_simple hz hs0 hs1)

end RHFinal

section Audit
#print axioms RHFinal.xiFn_differentiableAt
#print axioms RHFinal.RH_general
#print axioms RHFinal.RH_xi
#print axioms RHFinal.RH_xi_zeros
end Audit

end
