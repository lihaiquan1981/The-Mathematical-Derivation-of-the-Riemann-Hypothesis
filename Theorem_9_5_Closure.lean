module

/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

public import Lemma_9_4

@[expose] public section

open RH95C RH95U RH94

namespace RH95Final

def SatisfiesUnitarity (C : ℝ) (f : ℂ → ℂ) : Prop :=
  ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 → σ ≠ 1 / 2 → t ≠ 0 →
    0 < Kquad C (orbitGrad f σ t)

theorem theorem_9_5_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 →
      deriv f (↑σ + Complex.I * ↑t) ≠ 0)
    (hunit : SatisfiesUnitarity C f)
    {σ t : ℝ} (hz : f (↑σ + Complex.I * ↑t) = 0) (hσ : σ ≠ 1/2) (ht : t ≠ 0) :
    False := by

  have hdistinct : Function.Injective (orbit σ t) := orbit_injective hσ ht

  have e : (↑σ + ↑t * Complex.I : ℂ) = ↑σ + Complex.I * ↑t := by rw [mul_comm]
  have hv : nablaV f (σ, t) ≠ 0 := nablaV_ne_zero hf (by rw [e]; exact hsimple σ t hz)

  have hW : orbitGrad f σ t = chiABVec (nablaV f (σ, t)) := orbitGrad_eq hf h_sym h_conj σ t
  have hA : ∀ i, chiABVec (nablaV f (σ, t)) (iA i) = JB (chiABVec (nablaV f (σ, t)) i) :=
    chiABVec_A _
  have hB : ∀ i, chiABVec (nablaV f (σ, t)) (iB i) = JA (chiABVec (nablaV f (σ, t)) i) :=
    chiABVec_B _
  have hne : ∃ i, chiABVec (nablaV f (σ, t)) i ≠ 0 := chiABVec_nonzero hv

  have hpos : 0 < Kquad C (orbitGrad f σ t) := hunit σ t hz hσ ht

  have hneg : Kquad C (orbitGrad f σ t) < 0 := by
    rw [hW]
    exact Kquad_chiAB_neg C _ hC hA hB hne
  linarith

theorem theorem_10_final (C : ℝ) (hC : 0 < C)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f)
    (h_sym : ∀ s, f (1 - s) = f s) (h_conj : ∀ s, f (star s) = star (f s))
    (hsimple : ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 →
      deriv f (↑σ + Complex.I * ↑t) ≠ 0)
    (hunit : SatisfiesUnitarity C f) :
    ∀ σ t : ℝ, f (↑σ + Complex.I * ↑t) = 0 → σ ≠ 1/2 → t = 0 := by
  intro σ t hz hσ
  by_contra ht
  exact theorem_9_5_final C hC f hf h_sym h_conj hsimple hunit hz hσ ht

end RH95Final

section Audit
#print axioms RH95Final.theorem_9_5_final
#print axioms RH95Final.theorem_10_final
end Audit

end
