# Arquitetura Lean — Formalização da Cadeia C2 → RH

> **Documento de referência para implementação Lean 4 + Mathlib.**
>
> Mapa de o que formalizar, em que ordem, em quais arquivos, citando cada
> nota de prova-papel correspondente. Estratégia: **só formalizar o que é
> necessário** para a cadeia lógica fechar, **citar** input clássico
> (V-K Ford, Phragmén-Lindelöf, equação funcional) como `axiom` ou
> `Mathlib`.
>
> Lean 4 + Mathlib4 atual (toolchain `leanprover/lean4:v4.x`).
>
> **Princípio.** A teoria C2 original entra como definições e teoremas
> formalizados. O input clássico entra como hipótese declarada (axiom
> citando referência) ou via Mathlib quando disponível.

> **Nota de implementacao (2026-05-04).** O scaffold inicial ja foi criado
> neste repositorio em `Lean/`, seguindo o layout oficial do Lake atual:
> `lakefile.toml`, `lean-toolchain`, `LeanC2.lean` e a arvore `LeanC2/`.
> O codigo antigo foi preservado em `Lean/Antigo_Lean_C2/` e o mapa de
> migracao esta em `Lean/legacy_reuse_map.md`.

---

## Sumário

- [1. Princípios de design](#1-princípios-de-design)
- [2. Estrutura de diretórios](#2-estrutura-de-diretórios)
- [3. Módulos e dependências](#3-módulos-e-dependências)
- [4. O que formalizar (camada por camada)](#4-o-que-formalizar)
- [5. O que NÃO formalizar (axiomas declarados)](#5-o-que-não-formalizar)
- [6. Mapeamento doc → arquivo Lean](#6-mapeamento-doc--arquivo-lean)
- [7. Roadmap de implementação](#7-roadmap-de-implementação)
- [8. Convenções de naming e estilo](#8-convenções)
- [9. CI, build, e dependências externas](#9-ci-build-dependências)
- [10. Sketch de skeleton inicial](#10-sketch-de-skeleton-inicial)

---

## 1. Princípios de design

| Princípio | Aplicação |
|---|---|
| **Minimalidade** | Só o que está na cadeia lógica do Teorema RH (§5 de [c2_bulk_offaxis_transfer.md](c2_bulk_offaxis_transfer.md)). Notas de exploração ficam **fora**. |
| **Modularidade** | Cada teorema-chave em arquivo próprio, com `import` explícito. Sem god-files. |
| **Axiomas explícitos** | Input clássico (V-K Ford 2002, eq. funcional, Phragmén-Lindelöf) como `axiom` documentado com referência bibliográfica. |
| **Mathlib first** | Usar `Mathlib.NumberTheory.ZetaFunction`, `Mathlib.Analysis.Complex.*`, `Mathlib.NumberTheory.LSeries.*` quando disponível. Não reinventar. |
| **Numérico via `Decide`/`Nat.decide`** | Cálculos de constantes ($A=1{,}5862$, $K_1=57{,}54$ etc.) como `decide` ou `norm_num` com tolerância racional declarada. |
| **Sem `sorry` na cadeia principal** | `sorry` permitido só em lemmas auxiliares marcados como `-- TODO`. |

---

## 2. Estrutura de diretórios

```
Lean/
├── Antigo_Lean_C2/            -- codigo legado preservado
├── c2_lean_architecture.md    -- esta nota
├── legacy_reuse_map.md        -- mapa legado -> novo
├── lakefile.toml              -- configuracao Lake
├── lean-toolchain             -- versao Lean
├── LeanC2.lean                -- arquivo raiz (re-exporta tudo)
│
└── LeanC2/
  ├── Foundations/
│   ├── Basic.lean             -- s = σ + it, δ = σ - 1/2, c = 2^k m, etc.
│   ├── DyadicArith.lean       -- v_2, k_eff, bijeção centro↔perna (Thm 1)
│   ├── DiscreteLaplacian.lean -- Δ²[f](c) := f(c-1) + f(c+1) - 2f(c)
│   └── Tilt.lean              -- n^{-δ}, sign-definiteness (Thm 2, 5)
│
  ├── Operators/
│   ├── Branch.lean            -- W_∞(s), ‖·‖² = 2^{1-4σ}/(1-2^{-2σ})
│   ├── BranchNormBarrier.lean -- ‖W_∞‖² = 1 ⇔ σ = 1/2
│   ├── Genuine.lean           -- D, B, F = D - B
│   ├── Cutoff.lean            -- D_X, F_X = D_X - B
│   └── BranchToGenuine.lean   -- ponte branch → genuine (Thms da nota op_ramo)
│
  ├── Identity/
│   ├── C0.lean                -- c_0(s) = 2^{-2s}(2^s-1)/(2·2^s-1)
│   ├── C0NonZero.lean         -- Thm 14: c_0 ≠ 0 em 0 < σ < 1
│   ├── FundamentalIdentity.lean -- Thm 13: F_∞ = c_0 · ζ em σ > 1
│   └── MeromorphicExt.lean    -- Thm 17: continuação para σ > 0
│
  ├── Cutoff/
│   ├── Residue.lean           -- R_X = D_X - D_∞
│   ├── DecayRate.lean         -- Thm 16: |R_X| = O(1/X)
│   ├── Universality.lean      -- Thm 3: cutoffs Schwartz preservam seletividade
│   └── Cancellation.lean      -- Thm 4: |D_X - B_X| / |D_X| = O(1/X)
│
  ├── NearAxis/
│   ├── Transversality.lean    -- Thm 8: ∂^{m_ρ}(D-B)|_ρ = c_0(ρ) ζ^{(m_ρ)}(ρ) ≠ 0
│   ├── Amplification.lean     -- Thm 6: A(ρ, X) = O(X) → ∞
│   ├── TaylorRadius.lean      -- δ*(ρ) = 2 M_1 / M_2
│   ├── GlobalBound.lean       -- Thm 11: δ* ≥ 2/(2A + C log²γ), A=1.5862, C=0.169
│   └── FXNonZero.lean         -- Lema N: |F_X| > 0 em Ω_near^+
│
  ├── Bulk/
│   ├── Resolvent.lean         -- T_r(θ) = 1/(1 - re^{iθ}), inf = 1/(1+r)
│   ├── QuartetSharp.lean      -- inf|P_r| = (1-r)(1+r²)
│   ├── ClassicalAxioms.lean   -- AXIOMS: V-K Ford 2002, eq. funcional, Phragmén-Lindelöf
│   ├── BulkLowerBound.lean    -- Teorema 6.6: |F_∞| ≥ c_min · exp(-C*(log T)^{2/3+η})
│   └── FXNonZeroBulk.lean     -- Lema B: |F_X| > 0 em Ω_bulk^+
│
  ├── Edge/
│   ├── EdgeRight.lean         -- Lema R: borda direita via V-K
│   ├── EdgeLeft.lean          -- Lema L: borda esquerda via eq. funcional
│   └── FEdgeNonZero.lean      -- Lema F-edge: |F_X| > 0 em Ω_edge^+
│
  ├── Glue/
│   ├── Decomposition.lean     -- Lema 2.1: Ω ⊆ Ω_near^+ ∪ Ω_bulk^+ ∪ Ω_edge^+
│   ├── Compatibility.lean     -- Lemas 4.1, 4.2: overlaps consistentes
│   ├── UniformCutoff.lean     -- Lema 4.3: X(T) = X_bulk(T) suficiente
│   └── GlueTheorem.lean       -- Teorema da Colagem: F_X ≠ 0 em Ω
│
  ├── Finite/
│   ├── DyadicCoverage.lean    -- t ∈ [0, 448] zero-free (cobertura finita)
│   └── FiniteCertificate.lean -- import do certificado numérico (axiom ou tabela)
│
  ├── Transfer/
│   ├── Hurwitz.lean           -- F_X → F_∞ uniforme + F_X ≠ 0 ⇒ F_∞ ≠ 0
│   ├── ZetaTransfer.lean      -- Teorema Transfer: ζ ≠ 0 em Ω
│   └── RH.lean                -- Teorema RH em forma C2 (zeros não-triviais em σ=1/2)
│
  └── Numerical/
    ├── Constants.lean         -- A = 1.5862, C = 0.169, K_1, K_2, C_T, etc.
    └── Verification.lean      -- runs numéricos como axioms (com hash do log)
```

---

## 3. Módulos e dependências

Grafo de dependências (top-down):

```
                          RH.lean
                             |
                       ZetaTransfer.lean
                             |
                       Hurwitz.lean
                             |
                  ┌──────────┴──────────┐
                  |                      |
            GlueTheorem.lean      FiniteCertificate.lean
                  |
        ┌─────────┼─────────┐
        |         |         |
   FXNonZero  FXNonZeroBulk FEdgeNonZero
   (NearAxis) (Bulk)        (Edge)
        |         |         |
        |    BulkLowerBound  EdgeRight, EdgeLeft
        |    + ClassicalAxioms     |
        |                          |
        ├─── Transversality ────── C0NonZero ───┐
        |    + GlobalBound                        |
        |                                          |
        ├── MeromorphicExt ─────────────────────────┤
        |    + FundamentalIdentity                  |
        |                                          |
        ├── DecayRate (Cutoff)                     |
        |                                          |
        └── Genuine, Branch, BranchToGenuine ──────┤
                            |                      |
                       BranchNormBarrier            |
                            |                      |
              ┌─────────────┴──────────────┐       |
              |                            |       |
        DiscreteLaplacian, Tilt    DyadicArith    C0
              |                            |       |
              └──────── Basic ─────────────┘───────┘
```

---

## 4. O que formalizar

### Camada 0 — Foundations (~500 linhas)

**Objetivo:** definições básicas, álgebra binária, bracket, tilt sign.

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `Basic.lean` | `s : ℂ`, `σ := s.re`, `t := s.im`, `δ := σ - 1/2` | [derivacao_tilt_c2_global.md §1](derivacao_tilt_c2_global.md) |
| `DyadicArith.lean` | `v₂ : ℕ → ℕ`, `k_eff(n) := max(v₂(n-1), v₂(n+1))`, **bijeção Thm 1** | [c2_rota_K §2](c2_rota_K_rigorosamente_fechada.md) |
| `DiscreteLaplacian.lean` | `Δ² f c := f (c-1) + f (c+1) - 2 * f c`, propriedades básicas | [derivacao_tilt §1, §6](derivacao_tilt_c2_global.md) |
| `Tilt.lean` | `tilt δ n := (n : ℂ)^(-δ)`, **Thm 2** (`Δ²[tilt 0] = 0`), **Thm 5** (sign-def) | [c2_rota_K §6, §7](c2_rota_K_rigorosamente_fechada.md), [derivacao_tilt §3-§5](derivacao_tilt_c2_global.md) |

**Esforço:** baixo. Tudo é álgebra concreta + Jensen discreto. Mathlib tem `Convex.inner_le_iff`, `StrictConvex` — usar.

### Camada 1 — Operators (~800 linhas)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `Branch.lean` | `W_∞ s : ℓ²(ℕ) →L ℓ²(ℕ)`, `‖W_∞ s‖² = 2^{1-4σ}/(1-2^{-2σ})` | [nota_offaxis §2](nota_offaxis_c2.md), [c2_op_ramo_invariancia](c2_operador_ramo_invariancia_t_ponte_genuine.md) |
| `BranchNormBarrier.lean` | `‖W_∞ s‖² = 1 ↔ σ = 1/2` | [nota_offaxis §2.5](nota_offaxis_c2.md) |
| `Genuine.lean` | `D_∞`, `B_∞`, `F_∞ := D_∞ - B_∞` (Dirichlet series, σ > 1) | [c2_rota_K §1](c2_rota_K_rigorosamente_fechada.md) |
| `Cutoff.lean` | `D_X(s) := Σ w(n) n^{-s} e^{-n/X}`, `F_X` | [c2_cutoff_adaptativo_quarteto.md](c2_cutoff_adaptativo_quarteto.md) |
| `BranchToGenuine.lean` | ponte formal | [c2_op_ramo_invariancia §3](c2_operador_ramo_invariancia_t_ponte_genuine.md) |

**Esforço:** médio. Convergência absoluta e Fubini precisam de `Summable.tsum_*` de Mathlib.

### Camada 2 — Identity (~400 linhas)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `C0.lean` | `c_0 s := 2^(-2*s) * (2^s - 1) / (2 * 2^s - 1)` | [algebra_Z_igual_zeta.md](algebra_Z_igual_zeta.md) |
| `C0NonZero.lean` | **Thm 14**: `c_0 s ≠ 0` em `0 < σ < 1`. Lower bound `|c_0| ≥ 0.054` em σ=1/2. | [algebra_Z_igual_zeta.md](algebra_Z_igual_zeta.md) §3 |
| `FundamentalIdentity.lean` | **Thm 13**: `F_∞ s = c_0 s * ζ s` em σ > 1, via bijeção + Fubini | [c2_rota_K §3](c2_rota_K_rigorosamente_fechada.md) |
| `MeromorphicExt.lean` | **Thm 17**: continuação para σ > 0 via Teorema da Identidade | [c2_prova_continuacao_Z_zeta.md](c2_prova_continuacao_Z_zeta.md) |

**Esforço:** médio. `Mathlib.NumberTheory.ZetaFunction` tem `riemannZeta` com continuação meromorfa. Usar.

### Camada 3 — Cutoff (~300 linhas)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `DecayRate.lean` | **Thm 16**: `|R_X(s)| = O(1/X)` uniforme em compactos σ > 0 | [c2_prova_taxa_decaimento_cutoff.md](c2_prova_taxa_decaimento_cutoff.md), [nota_cutoff_c2.md](nota_cutoff_c2.md) |
| `Cancellation.lean` | **Thm 4**: `|D_X - B_X| ≤ C/X` (cancela O(X):1) | [c2_rota_K §9](c2_rota_K_rigorosamente_fechada.md) |
| `Universality.lean` | **Thm 3**: cutoffs Schwartz | [c2_rota_K §8](c2_rota_K_rigorosamente_fechada.md) |

**Esforço:** baixo. `Mathlib.MeasureTheory.Integral.DominatedConvergence`.

### Camada 4 — NearAxis (~600 linhas)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `Transversality.lean` | **Thm 8**: `(d/ds)^{m_ρ} F_∞ \|_ρ = c_0(ρ) ζ^{(m_ρ)}(ρ) ≠ 0` via Leibniz | [c2_prova_thm8_transversal.md](c2_prova_thm8_transversal.md) |
| `Amplification.lean` | **Thm 6**: `A(ρ, X) = O(X)` | [c2_rota_K §13](c2_rota_K_rigorosamente_fechada.md) |
| `TaylorRadius.lean` | `δ*(ρ) := 2 M_1(ρ) / M_2(ρ)` | [c2_lower_bound_transversal_taylor.md](c2_lower_bound_transversal_taylor.md) |
| `GlobalBound.lean` | **Thm 11**: `δ*(ρ) ≥ 2 / (2A + C * (log γ)^2)` | [c2_certificacao_bound_global.md](c2_certificacao_bound_global.md) |
| `FXNonZero.lean` | **Lema N**: `F_X s ≠ 0` para `s ∈ Ω_near^+`, `t ≥ T_0` | [c2_bulk_offaxis_glue.md §3](c2_bulk_offaxis_glue.md) |

**Esforço:** alto. Thm 11 usa fórmula de Hadamard + von Mangoldt — pesado. Pode ser `axiom` citando prova papel se Mathlib não tiver Hadamard.

### Camada 5 — Bulk (~400 linhas, das quais ~100 são axiomas)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `Resolvent.lean` | `T_r θ := 1/(1 - r * exp(I*θ))`, `inf‖T_r‖ = 1/(1+r)` | [c2_quarteto_resolvente_sharpening.md](c2_quarteto_resolvente_sharpening.md) §3 |
| `QuartetSharp.lean` | `inf‖P_r‖ = (1-r)(1+r²)` | [c2_quarteto_resolvente_sharpening.md](c2_quarteto_resolvente_sharpening.md) §2 |
| `ClassicalAxioms.lean` | `axiom VK_Ford : ∀ t ≥ 3, ∀ σ ≥ σ_VK(t), \|ζ(σ+it)\| ≥ 1/(K₂ * (log t)^(2/3) * (loglog t)^(1/3))` + Phragmén-Lindelöf + eq. funcional | [c2_bulk_offaxis_route3_tilt.md §6.2-§6.4](c2_bulk_offaxis_route3_tilt.md) |
| `BulkLowerBound.lean` | **Teorema 6.6**: `\|F_∞ s\| ≥ c_min · exp(-C* * (log T)^(2/3+η))` | [c2_bulk_offaxis_route3_tilt.md §6.6](c2_bulk_offaxis_route3_tilt.md) |
| `FXNonZeroBulk.lean` | **Lema B**: `F_X s ≠ 0` em `Ω_bulk^+` | [c2_bulk_offaxis_glue.md §3](c2_bulk_offaxis_glue.md) |

**Esforço:** baixo (Resolvent é álgebra), média na composição BulkLowerBound. **Os clássicos são axiomas** com referência Ford 2002 / Titchmarsh.

### Camada 6 — Edge (~300 linhas)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `EdgeRight.lean` | **Lema R**: V-K Ford direto, T_0(ε) explícito | [c2_bulk_offaxis_edge_lemma.md §2](c2_bulk_offaxis_edge_lemma.md) |
| `EdgeLeft.lean` | **Lema L**: equação funcional + Stirling | [c2_bulk_offaxis_edge_lemma.md §3](c2_bulk_offaxis_edge_lemma.md) |
| `FEdgeNonZero.lean` | **Lema F-edge**: lifting ζ → F_∞ → F_X via c_0 ≠ 0 | [c2_bulk_offaxis_edge_lemma.md §4](c2_bulk_offaxis_edge_lemma.md) |

### Camada 7 — Glue (~250 linhas)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `Decomposition.lean` | **Lema 2.1**: cobertura por overlaps | [c2_bulk_offaxis_glue.md §2](c2_bulk_offaxis_glue.md) |
| `Compatibility.lean` | **Lemas 4.1, 4.2**: bulk ≥ near, bulk ≥ edge nas overlaps | [c2_bulk_offaxis_glue.md §4](c2_bulk_offaxis_glue.md) |
| `UniformCutoff.lean` | **Lema 4.3**: `X(T) = X_bulk(T)` suficiente para todas as três regiões | [c2_bulk_offaxis_glue.md §4.3](c2_bulk_offaxis_glue.md) |
| `GlueTheorem.lean` | **Teorema da Colagem**: `F_X s ≠ 0` em `Ω`, `t ≥ T_0 = 100` | [c2_bulk_offaxis_glue.md §5](c2_bulk_offaxis_glue.md) |

### Camada 8 — Finite (~100 linhas, mais axioma de certificado)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `FiniteCertificate.lean` | `axiom finite_zero_free : ∀ s ∈ Ω, t ≤ 448, F_X s ≠ 0` (citando log do scan) | [teorema_faixa_diadica_zero_free.md](teorema_faixa_diadica_zero_free.md) |
| `DyadicCoverage.lean` | enunciado formal do certificado, sem prova interna | idem |

> **Nota.** Verificação numérica de cobertura finita é difícil de internalizar
> em Lean. Padrão aceito: declarar axioma referenciando hash SHA-256 do
> log de saída + script reprodutível.

### Camada 9 — Transfer + RH (~200 linhas)

| Arquivo | Conteúdo | Doc-fonte |
|---|---|---|
| `Hurwitz.lean` | `F_X → F_∞` uniforme + `F_X ≠ 0 ∀X ⇒ F_∞ ≠ 0 ou F_∞ ≡ 0` | [c2_bulk_offaxis_transfer.md §3](c2_bulk_offaxis_transfer.md) |
| `ZetaTransfer.lean` | **Teorema Transfer**: `ζ s ≠ 0` em `Ω` | [c2_bulk_offaxis_transfer.md §4](c2_bulk_offaxis_transfer.md) |
| `RH.lean` | **Teorema RH**: zeros não-triviais em `σ = 1/2` | [c2_bulk_offaxis_transfer.md §5](c2_bulk_offaxis_transfer.md) |

**Esforço:** baixo. Hurwitz está em `Mathlib.Analysis.Complex.Hurwitz` (verificar nome exato).

---

## 5. O que NÃO formalizar (axiomas declarados)

Isolados em `Bulk/ClassicalAxioms.lean` + `Edge/*.lean` + `Finite/FiniteCertificate.lean`:

| Axioma | Origem | Justificativa |
|---|---|---|
| `axiom VK_Ford_2002` | Ford, *Vinogradov's integral and bounds for ζ*, Proc LMS 85 (2002) | Resultado clássico, replicado, não-circular. |
| `axiom functional_equation` | Riemann 1859, Titchmarsh §2.1 | Em Mathlib como `Complex.riemannZeta_functional_equation`? Verificar. |
| `axiom phragmen_lindelof_strip` | Titchmarsh §5.65 | Em Mathlib como `Complex.PhragmenLindelof.*`. |
| `axiom hadamard_product_zeta` | Hadamard 1893 | Pode estar em Mathlib (LSeries.HadamardProduct). |
| `axiom finite_zero_free_to_448` | Run de [scripts/c2_zero_detector_genuine.py](../scripts/c2_zero_detector_genuine.py) | Cita SHA-256 do log + reprodutibilidade. |
| `axiom rouche_pilot_T500` | Run de [scripts/c2_rouche_rectangle.py](../scripts/c2_rouche_rectangle.py) | Opcional — não está na cadeia mínima. |

> **Recomendação.** Cada `axiom` vem com docstring contendo: (i) referência
> bibliográfica completa, (ii) enunciado em prosa, (iii) link para nota
> interna que cita a referência.

---

## 6. Mapeamento doc → arquivo Lean

Tabela inversa (cada nota → onde formaliza):

| Documento | Arquivos Lean correspondentes |
|---|---|
| [c2_rota_K_rigorosamente_fechada.md](c2_rota_K_rigorosamente_fechada.md) | `Foundations/*`, `Identity/*`, `Cutoff/*`, `NearAxis/Transversality.lean` |
| [algebra_Z_igual_zeta.md](algebra_Z_igual_zeta.md) | `Identity/C0.lean`, `Identity/C0NonZero.lean`, `Identity/FundamentalIdentity.lean` |
| [c2_prova_continuacao_Z_zeta.md](c2_prova_continuacao_Z_zeta.md) | `Identity/MeromorphicExt.lean` |
| [c2_prova_thm8_transversal.md](c2_prova_thm8_transversal.md) | `NearAxis/Transversality.lean` |
| [c2_certificacao_bound_global.md](c2_certificacao_bound_global.md) | `NearAxis/GlobalBound.lean`, `Numerical/Constants.lean` |
| [c2_lower_bound_transversal_taylor.md](c2_lower_bound_transversal_taylor.md) | `NearAxis/TaylorRadius.lean`, `NearAxis/GlobalBound.lean` |
| [c2_cutoff_adaptativo_quarteto.md](c2_cutoff_adaptativo_quarteto.md) | `Operators/Cutoff.lean`, `Cutoff/DecayRate.lean` |
| [c2_prova_taxa_decaimento_cutoff.md](c2_prova_taxa_decaimento_cutoff.md) | `Cutoff/DecayRate.lean` |
| [c2_quarteto_resolvente_sharpening.md](c2_quarteto_resolvente_sharpening.md) | `Bulk/Resolvent.lean`, `Bulk/QuartetSharp.lean` |
| [nota_offaxis_c2.md](nota_offaxis_c2.md) | `Operators/Branch.lean`, `Operators/BranchNormBarrier.lean` |
| [c2_operador_ramo_invariancia_t_ponte_genuine.md](c2_operador_ramo_invariancia_t_ponte_genuine.md) | `Operators/BranchToGenuine.lean` |
| [c2_bulk_offaxis_route3_tilt.md](c2_bulk_offaxis_route3_tilt.md) | `Bulk/ClassicalAxioms.lean`, `Bulk/BulkLowerBound.lean` |
| [c2_bulk_offaxis_route2_rouche.md](c2_bulk_offaxis_route2_rouche.md) | (opcional, não na cadeia mínima) |
| [c2_bulk_offaxis_edge_lemma.md](c2_bulk_offaxis_edge_lemma.md) | `Edge/EdgeRight.lean`, `Edge/EdgeLeft.lean`, `Edge/FEdgeNonZero.lean` |
| [c2_bulk_offaxis_glue.md](c2_bulk_offaxis_glue.md) | `Glue/*.lean` |
| [c2_bulk_offaxis_transfer.md](c2_bulk_offaxis_transfer.md) | `Transfer/*.lean`, `RH.lean` |
| [teorema_faixa_diadica_zero_free.md](teorema_faixa_diadica_zero_free.md) | `Finite/FiniteCertificate.lean` (axioma) |
| [hadamard_von_mongoldt.md](hadamard_von_mongoldt.md) | usado em `NearAxis/GlobalBound.lean` (axioma se Mathlib não cobrir) |

Documentos **não formalizados** (são exploração/diagnóstico, fora da cadeia):

- [c2_pure_carry_barrier_attempt.md](c2_pure_carry_barrier_attempt.md) — exploração negativa
- [c2_lambda_*.md](c2_lambda_estrutura_profunda.md) — análises tangenciais
- [cadeia_unica.md](cadeia_unica.md), [fechamento_unificado.md](fechamento_unificado.md) — sínteses, redundantes com cadeia formal
- [c2_inversao_zeros_via_FFT.md](c2_inversao_zeros_via_FFT.md), [c2_dualidade_primo_zero.md](c2_dualidade_primo_zero.md) — exploração
- Notas com sufixos `_atualizada`, `_OLF`, etc. — versões superseded

---

## 7. Roadmap de implementação

Fases sugeridas em ordem de execução. Cada fase produz um build verde antes de seguir.

### Fase 0 — Setup (1 sessão)

1. `lake new LeanC2` em diretório novo (fora deste repo, ou em `lean/` aqui)
2. Adicionar Mathlib em `lakefile.lean`
3. Criar estrutura de diretórios vazia (todos os arquivos com `import Mathlib` + skeleton)
4. CI básico: `lake build` no GitHub Actions

### Fase 1 — Foundations (2-3 sessões)

`Basic.lean`, `DyadicArith.lean`, `DiscreteLaplacian.lean`, `Tilt.lean`.
Marco: **Thm 2 e Thm 5 formalizados**.

### Fase 2 — Identity (3-4 sessões)

`C0.lean`, `C0NonZero.lean`, `FundamentalIdentity.lean`, `MeromorphicExt.lean`.
Marco: **`F_∞ = c_0 * ζ` em `σ > 0`** (Thms 13 + 17).

### Fase 3 — Operators + Cutoff (4-5 sessões)

`Genuine.lean`, `Cutoff.lean`, `DecayRate.lean`, `Branch.lean`.
Marco: **`|F_X - F_∞| ≤ C/X`** (Thm 16) e barreira `‖W_∞‖² = 1 ⇔ σ=1/2`.

### Fase 4 — NearAxis (5-6 sessões, parte mais técnica)

Marco: **Thm 8 (transversalidade) + Thm 11 (bound global $\delta^*$)**.

### Fase 5 — Bulk + Edge (3-4 sessões, muitos axiomas)

`ClassicalAxioms.lean` define V-K + Phragmén + eq. funcional como axioma.
Marco: **Lemas N, B, E formalizados**.

### Fase 6 — Glue + Transfer (2-3 sessões)

Marco: **Teorema da Colagem + Teorema RH**.

### Fase 7 — Polimento (~1-2 sessões)

- Verificar `#check @riemann_hypothesis_C2`
- Auditar lista de axiomas: `#print axioms riemann_hypothesis_C2`
- Documentação Sphinx ou doc-gen4

**Total estimado:** 20-30 sessões para versão funcional.

---

## 8. Convenções

### Naming

- Definições: `camelCase` (Mathlib style): `branchOperator`, `cutoffResidue`.
- Teoremas: `snake_case_descriptive`: `branch_norm_eq_one_iff_sigma_half`, `c0_ne_zero_of_open_strip`.
- Numerais por extenso: `theorem_eight_transversality` (referenciando o "Teorema 8").

### Estrutura típica de arquivo

```lean
/-
Copyright © 2026 [autor].
Released under Apache 2.0 license as described in LICENSE.
Author: [user].

Reference: docs/c2_rota_K_rigorosamente_fechada.md §6.
-/
import Mathlib.Analysis.Complex.Basic
import LeanC2.Foundations.Basic
import LeanC2.Foundations.DiscreteLaplacian

namespace LeanC2

/-- Doc-string descrevendo o conteúdo. -/
theorem theorem_two_tilt_annihilation (c : ℕ) (hc : 4 ≤ c) (δ : ℝ) :
    discreteLaplacian (fun n => (n : ℝ) ^ (-δ)) c = 0 ↔ δ = 0 := by
  sorry  -- TODO: prova via convexidade estrita

end LeanC2
```

### Axiomas

```lean
/-- **Vinogradov–Korobov, Ford 2002.**

Reference: K. Ford, *Vinogradov's integral and bounds for the Riemann
zeta function*, Proc. London Math. Soc. **85** (2002), Thm 3.

Constants: K₁ = 57.54, K₂ = 76.2.

Internal note: docs/c2_bulk_offaxis_route3_tilt.md §6.2.
-/
axiom VK_Ford_2002 :
    ∀ t : ℝ, 3 ≤ |t| →
    ∀ σ : ℝ, σ ≥ 1 - 1 / (57.54 * Real.log |t| ^ ((2:ℝ)/3) * Real.log (Real.log |t|) ^ ((1:ℝ)/3)) →
    ‖riemannZeta (σ + t * I)‖ ≥
      1 / (76.2 * Real.log |t| ^ ((2:ℝ)/3) * Real.log (Real.log |t|) ^ ((1:ℝ)/3))
```

### Constantes numéricas

Em `Numerical/Constants.lean`, declarar como `def` racional ou `theorem` com `norm_num`:

```lean
/-- Constante A do bound global, A = 1.5862. -/
noncomputable def constA : ℝ := 7931 / 5000  -- = 1.5862

theorem constA_eq : constA = 1.5862 := by norm_num [constA]
```

---

## 9. CI, build, dependências

`lakefile.toml`:

```toml
name = "LeanC2"
version = "0.1.0"
defaultTargets = ["LeanC2"]

[leanOptions]
pp.unicode.fun = true
relaxedAutoImplicit = false
weak.linter.mathlibStandardSet = true
maxSynthPendingDepth = 3

[[require]]
name = "mathlib"
scope = "leanprover-community"
rev = "v4.29.1"

[[lean_lib]]
name = "LeanC2"
```

`lean-toolchain`:

```
leanprover/lean4:v4.29.1
```

GitHub Actions (`.github/workflows/build.yml`):

```yaml
on: [push, pull_request]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
      - run: lake exe cache get && lake build
      - run: |
          # Auditar axiomas usados pelo teorema final
          echo '#print axioms LeanC2.Transfer.RH.riemann_hypothesis_C2' >> AuditAxioms.lean
          lake env lean AuditAxioms.lean
```

---

## 10. Sketch de skeleton inicial

Sugestão para o `LeanC2.lean` raiz (re-export):

```lean
import LeanC2.Foundations.Basic
import LeanC2.Foundations.DyadicArith
import LeanC2.Foundations.DiscreteLaplacian
import LeanC2.Foundations.Tilt

import LeanC2.Operators.Branch
import LeanC2.Operators.BranchNormBarrier
import LeanC2.Operators.Genuine
import LeanC2.Operators.Cutoff
import LeanC2.Operators.BranchToGenuine

import LeanC2.Identity.C0
import LeanC2.Identity.C0NonZero
import LeanC2.Identity.FundamentalIdentity
import LeanC2.Identity.MeromorphicExt

import LeanC2.Cutoff.DecayRate
import LeanC2.Cutoff.Universality
import LeanC2.Cutoff.Cancellation

import LeanC2.NearAxis.Transversality
import LeanC2.NearAxis.Amplification
import LeanC2.NearAxis.TaylorRadius
import LeanC2.NearAxis.GlobalBound
import LeanC2.NearAxis.FXNonZero

import LeanC2.Bulk.Resolvent
import LeanC2.Bulk.QuartetSharp
import LeanC2.Bulk.ClassicalAxioms
import LeanC2.Bulk.BulkLowerBound
import LeanC2.Bulk.FXNonZeroBulk

import LeanC2.Edge.EdgeRight
import LeanC2.Edge.EdgeLeft
import LeanC2.Edge.FEdgeNonZero

import LeanC2.Glue.Decomposition
import LeanC2.Glue.Compatibility
import LeanC2.Glue.UniformCutoff
import LeanC2.Glue.GlueTheorem

import LeanC2.Finite.FiniteCertificate

import LeanC2.Transfer.Hurwitz
import LeanC2.Transfer.ZetaTransfer
import LeanC2.Transfer.RH
```

E o teorema final em `Transfer/RH.lean`:

```lean
/-- **Hipótese de Riemann (forma C2).**

Todos os zeros não-triviais de `riemannZeta` têm parte real `1/2`.

Referência: docs/c2_bulk_offaxis_transfer.md §5.

Inputs clássicos (axiomas em `Bulk.ClassicalAxioms`):
  - V-K Ford 2002 (Theorem 3)
  - Equação funcional + Stirling
  - Phragmén-Lindelöf

Input numérico (axioma em `Finite.FiniteCertificate`):
  - Cobertura finita t ∈ [0, 448] via scripts/c2_zero_detector_genuine.py
-/
theorem riemann_hypothesis_C2 :
    ∀ s : ℂ, riemannZeta s = 0 → s.re ≤ 0 ∨ s.re ≥ 1 ∨ s.re = 1/2 := by
  sorry
```

> Note que o enunciado RH no Mathlib é
> `Complex.riemannHypothesis : ∀ s, riemannZeta s = 0 → s ∈ trivialZeroSet ∨ s.re = 1/2`.
> Use o nome canônico Mathlib para que `#check` confirme alinhamento.

---

## 11. Referências bibliográficas externas (para axiomas)

| Referência | Uso |
|---|---|
| Ford, K. *Vinogradov's integral and bounds for ζ*. Proc LMS 85 (2002). | V-K efetivo |
| Titchmarsh, E.C. *The Theory of the Riemann Zeta-Function*, 2nd ed. (Heath-Brown), Oxford 1986. | Phragmén-Lindelöf §5.65, eq. funcional §2 |
| Iwaniec & Kowalski, *Analytic Number Theory*, AMS 2004. | Density estimates, Hadamard |
| Edwards, H.M. *Riemann's Zeta Function*. | Background histórico |
| Mossinghoff & Trudgian, *Nonnegative trigonometric polynomials and a zero-free region for ζ*, J. Number Theory (2015). | Refinamentos V-K |

---

## 12. Status e próximas decisões

| Item | Estado |
|---|---|
| Arquitetura desenhada | ✅ este documento |
| Repositório Lean | ❌ a criar (`lake new LeanC2`) |
| Fase 0 (setup) | ⏳ próxima |
| Fases 1-7 | ⏳ a implementar |

**Decisões de design pendentes:**

1. Repositório Lean **dentro** deste workspace (`lean/`) ou **separado** (mais limpo, melhor para CI independente)?
2. Mathlib quanto: usar versão pinned ou bleeding edge?
3. Documentação paralela: `doc-gen4` ou só docstrings?

Recomendação: **diretório `lean/` aqui dentro**, Mathlib pinned na versão estável atual, docstrings em português (autoria) + nomes de teoremas em inglês (compatibilidade Mathlib).
