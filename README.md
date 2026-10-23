Li Haiquan
Jilin University of Chemical Technology, China
ORCID: https://orcid.org/0009-0000-7365-6535
Email: lihaiquan@jluct.edu.cn

# Double-reflection lemmas for ξ in Lean 4

This repository contains Lean theorems about entire functions `f` with `f (1 - s) = f s` and
`f (conj s) = conj (f s)`, and about Riemann's ξ. The statements Palomar
compares are in `Challenge.lean`, proved in `Solution.lean`; `comparator.json`
lists them. The assemblies are conditional: they hold under the hypotheses on
their signatures, which are not proved here. This repository does not prove
the Riemann Hypothesis. Labels such as "Lemma 9.4" are the author's own
numbering.

## Build

Lean `v4.35.0-rc2`, mathlib `v4.35.0-rc2`.

```bash
lake update
lake exe cache get
lake build
```

## Files

| File | Content |
|---|---|
| `MotherEquation_CoreVerification.lean` | Integer sign certificates |
| `Theorem_9_3A.lean` | Even reduction `f s = g ((s - 1/2)^2)` |
| `Lemma_9_4.lean` | Reflection laws and gradient of `Im f` |
| `Lemma_9_5C.lean`, `Lemma_9_5C_TaylorRemainder.lean` | Sign of `Kquad` on χAB configurations; Taylor remainder |
| `Unitarity_Assembly.lean`, `Theorem_9_5_Closure.lean` | Theorems 9.5 and 10 under `hunit` |
| `Lemma_11_3.lean` | ξ is real and positive at real points other than 0, 1, under `hζ` |
| `Final_Assembly.lean` | Assemblies for simple zeros |
| `Note_9_5B_mJet.lean`, `Final_Assembly_Unconditional.lean` | Assemblies for zeros of any multiplicity |
| `Section5A8_Unitarity.lean` | Five-way equivalence under `hSpec` |

## Hypotheses kept on the signatures

- `hsimple`, `hg_simple`: all zeros are simple, in the simple-zero assemblies.
- `hunit`: positivity of `Kquad` on the orbit gradient of a zero off the
  critical line and off the real axis.
- `hE_pos`, `hE_neg`: sign conditions on a real-valued function `E` of jets.
- `hζ`: `ζ` is negative on `(0, 1)`.
- `hBd`: bounded second derivative, in `taylor_remainder_C2`.
- `hSpec`: `Set.range α = Z`, in `five_eight_equiv`.