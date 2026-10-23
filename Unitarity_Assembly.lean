module

/-
Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn
-/

public import Lemma_9_5C

@[expose] public section

open RH95C

namespace RH95U

def orbit (σ t : ℝ) : Fin 4 → ℝ × ℝ := ![(σ, t), (1 - σ, t), (σ, -t), (1 - σ, -t)]

def reflA (u : ℝ × ℝ) : ℝ × ℝ := (1 - u.1, u.2)

def reflB (u : ℝ × ℝ) : ℝ × ℝ := (u.1, -u.2)

lemma iA_involutive : ∀ i : Fin 4, iA (iA i) = i := by decide

lemma iB_involutive : ∀ i : Fin 4, iB (iB i) = i := by decide

lemma orbit_iA (σ t : ℝ) : ∀ i : Fin 4, orbit σ t (iA i) = reflA (orbit σ t i) := by
  intro i
  fin_cases i <;> simp [orbit, iA, reflA]

lemma orbit_iB (σ t : ℝ) : ∀ i : Fin 4, orbit σ t (iB i) = reflB (orbit σ t i) := by
  intro i
  fin_cases i <;> simp [orbit, iB, reflB]

lemma orbit_injective {σ t : ℝ} (hσ : σ ≠ 1/2) (ht : t ≠ 0) :
    Function.Injective (orbit σ t) := by
  intro i j hij
  rcases lt_or_gt_of_ne hσ with hσ | hσ <;>
  rcases lt_or_gt_of_ne ht with ht | ht <;>
  fin_cases i <;> fin_cases j <;>
    first | rfl | (exfalso; simp [orbit, Prod.ext_iff] at hij; linarith)

def chiABVec (v : ℝ × ℝ) : Fin 4 → ℝ × ℝ := ![v, JB v, JA v, (-v.1, -v.2)]

lemma chiABVec_A (v : ℝ × ℝ) : ∀ i : Fin 4, chiABVec v (iA i) = JB (chiABVec v i) := by
  intro i
  fin_cases i <;> simp [chiABVec, iA, JB, JA]

lemma chiABVec_B (v : ℝ × ℝ) : ∀ i : Fin 4, chiABVec v (iB i) = JA (chiABVec v i) := by
  intro i
  fin_cases i <;> simp [chiABVec, iB, JB, JA]

lemma chiABVec_nonzero {v : ℝ × ℝ} (hv : v ≠ 0) : ∃ i : Fin 4, chiABVec v i ≠ 0 :=
  ⟨0, by simpa [chiABVec] using hv⟩

def UnitarityPositive (C : ℝ) : Prop :=
  ∀ w : Fin 4 → ℝ × ℝ,
    (∀ i, w (iA i) = JB (w i)) → (∀ i, w (iB i) = JA (w i)) →
    (∃ i, w i ≠ 0) → 0 < Kquad C w

theorem theorem_9_5 (C : ℝ) (hC : 0 < C) (hunit : UnitarityPositive C)
    {σ t : ℝ} (hσ : σ ≠ 1/2) (ht : t ≠ 0)
    {v : ℝ × ℝ} (hv : v ≠ 0) : False := by

  have hdistinct : Function.Injective (orbit σ t) := orbit_injective hσ ht
  have hA := chiABVec_A v
  have hB := chiABVec_B v
  have hne := chiABVec_nonzero hv
  have hneg := Kquad_chiAB_neg C (chiABVec v) hC hA hB hne
  have hpos := hunit (chiABVec v) hA hB hne
  linarith

theorem theorem_10 (C : ℝ) (hC : 0 < C) (hunit : UnitarityPositive C)
    (f : ℂ → ℂ)
    (hgrad : ∀ σ t : ℝ, f (σ + Complex.I * t) = 0 → σ ≠ 1/2 → t ≠ 0 →
      ∃ v : ℝ × ℝ, v ≠ 0) :
    ∀ σ t : ℝ, f (σ + Complex.I * t) = 0 → σ ≠ 1/2 → t = 0 := by
  intro σ t hz hσ
  by_contra ht
  obtain ⟨v, hv⟩ := hgrad σ t hz hσ ht
  exact theorem_9_5 C hC hunit hσ ht hv

end RH95U

section Audit
#print axioms RH95U.orbit_injective
#print axioms RH95U.chiABVec_A
#print axioms RH95U.chiABVec_B
#print axioms RH95U.chiABVec_nonzero
#print axioms RH95U.theorem_9_5
#print axioms RH95U.theorem_10
end Audit

end
