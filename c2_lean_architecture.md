# Arquitetura Lean — Estado Atual da Cadeia C2 → RH

> **Documento vivo de arquitetura e status do projeto Lean 4 + Mathlib.**
>
> Este arquivo nao descreve mais apenas um plano futuro. Ele registra o
> estado real do repositorio `Lean/`, o que ja esta build-clean, quais
> camadas estao fechadas em Lean, e quais pontos ainda entram como
> interface ou input classico.
>
> Atualizado em **2026-05-04**.
>
> Toolchain atual: Lean `v4.29.1`, Mathlib `v4.29.1`.

---

## Sumário

- [1. Princípios de design](#1-princípios-de-design)
- [2. Estrutura de diretórios](#2-estrutura-de-diretórios)
- [3. Módulos e dependências](#3-módulos-e-dependências)
- [4. Estado por camada](#4-estado-por-camada)
- [5. O que ainda entra como input externo](#5-o-que-ainda-entra-como-input-externo)
- [6. Mapeamento doc → arquivo Lean](#6-mapeamento-doc--arquivo-lean)
- [7. Endpoints e APIs já expostos](#7-endpoints-e-apis-já-expostos)
- [8. Build, toolchain e CI](#8-build-toolchain-e-ci)
- [9. Convenções de manutenção](#9-convenções-de-manutenção)
- [10. Próximos passos realistas](#10-próximos-passos-realistas)
- [11. Referências externas](#11-referências-externas)
- [12. Status resumido](#12-status-resumido)

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
## 2. Estrutura de diretórios

Estrutura real hoje:

```
/home/thlinux/C2_Hipotese_De_Riemann/
├── docs/
│   ├── c2_lean_architecture.md
│   └── c2_resumo_formalizacao_lean.md
└── Lean/
    ├── .git/
    ├── .lake/
    ├── Antigo_Lean_C2/
    ├── LeanC2/
    │   ├── Foundations/
    │   ├── Operators/
    │   ├── Identity/
    │   ├── Cutoff/
    │   ├── NearAxis/
    │   ├── Bulk/
    │   ├── Edge/
    │   ├── Glue/
    │   ├── Finite/
    │   ├── Transfer/
    │   └── Numerical/
    ├── LeanC2.lean
    ├── README.md
    ├── c2_lean_architecture.md
    ├── legacy_reuse_map.md
    ├── lake-manifest.json
    ├── lakefile.toml
    └── lean-toolchain
```

Notas importantes:

- o repositorio Lean real e o diretorio `Lean/`, nao a raiz do workspace;
- o arquivo raiz `Lean/LeanC2.lean` ja reexporta toda a arvore atual;
- o legado foi preservado em `Lean/Antigo_Lean_C2/`;
- este documento tem uma copia sincronizada em `Lean/c2_lean_architecture.md`.

---

## 3. Módulos e dependências

Fluxo logico atual, em alto nivel:

```
Foundations / Operators / Identity
        |
        +--> NearAxis
        +--> Bulk
        +--> Edge
        +--> Glue.Decomposition

NearAxis + Bulk + Edge
        |
        +--> Glue.UniformCutoff
        +--> Glue.GlueTheorem

Glue.GlueTheorem + Finite.FiniteCertificate
        |
        +--> Transfer.Hurwitz
        +--> Transfer.ZetaTransfer
        +--> Transfer.RH
```

Rota canonica default ja exposta hoje:

```
deltaStarLowerModel
   -> DefaultGlobalBoundData
   -> cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultGlobalBoundData
   -> hurwitzTransferOffCriticalStrip
   -> riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData
   -> riemannHypothesisC2_of_defaultGlobalBoundData
   -> routeK_default_globalBound_chain_RH
```

Em outras palavras: a cadeia default `finite + high glue + canonical global
bound` ja chega a um endpoint formal de RH em forma C2, ainda que a passagem
de Hurwitz e alguns insumos bulk/edge permaneçam como interface classica.

---

## 4. Estado por camada

Legenda:

- **Fechado**: definicoes e teoremas internos ja formalizados em Lean.
- **Parcial**: camada util e compilando, mas ainda com interfaces, witnesses abstratos ou pacotes intermediarios.
- **Axiomatico**: a camada ainda consome input classico ou certificado externo explicitamente.

| Camada | Status | Arquivos principais | Estado atual |
|---|---|---|---|
| Foundations | **Fechado** | `Foundations/Basic.lean`, `DyadicArith.lean`, `DiscreteLaplacian.lean`, `Tilt.lean` | Nucleo discreto/algebrico base da teoria C2 ja formalizado. |
| Operators | **Fechado** | `Operators/Branch.lean`, `BranchNormBarrier.lean`, `Genuine.lean`, `Cutoff.lean`, `BranchToGenuine.lean` | Camada dos operadores e do numerador `F` ja organizada e build-clean. |
| Identity | **Fechado** | `Identity/C0.lean`, `C0NonZero.lean`, `FundamentalIdentity.lean`, `MeromorphicExt.lean` | Ja formaliza `c0`, a nao anulacao de `c0` e a passagem `F = c0 * zeta` com extensao meromorfa no formato usado pela cadeia final. |
| Cutoff | **Parcial** | `Cutoff/Residue.lean`, `DecayRate.lean`, `Universality.lean`, `Cancellation.lean` | Camada presente e integrada, mas hoje funciona principalmente como infraestrutura para glue/Hurwitz. |
| NearAxis | **Parcial forte** | `NearAxis/Transversality.lean`, `TaylorRadius.lean`, `GlobalBound.lean`, `FXNonZero.lean`, `Amplification.lean` | Ja contem o nucleo abstrato de Thm 8, a algebra de Taylor, `deltaStarLowerModel` e a ponte de witnesses para `nearRegionEventuallyNonvanishing`; a producao analitica concreta desses witnesses ainda nao esta internalizada. |
| Bulk | **Parcial / Axiomatico** | `Bulk/Resolvent.lean`, `QuartetSharp.lean`, `ClassicalAxioms.lean`, `BulkLowerBound.lean`, `FXNonZeroBulk.lean` | Estrutura pronta e conectada, mas o lower bound pesado ainda depende de input classico e `FXNonZeroBulk` segue como interface operacional. |
| Edge | **Parcial** | `Edge/EdgeRight.lean`, `Edge/EdgeLeft.lean`, `FEdgeNonZero.lean` | A camada existe, mas a forma final usada na colagem ainda esta exposta como interface. |
| Glue | **Fechado** | `Glue/Decomposition.lean`, `Compatibility.lean`, `UniformCutoff.lean`, `GlueTheorem.lean` | Geometria off-axis, cobertura `near/bulk/edge`, compatibilidade e teorema de colagem high-height ja formalizados. |
| Finite | **Parcial / Axiomatico** | `Finite/DyadicCoverage.lean`, `FiniteCertificate.lean` | A cobertura finita e o empacotamento `finite + glue` existem, inclusive com `DefaultFiniteAndGlueData` e `DefaultGlobalBoundData`; o certificado numerico bruto ainda nao foi internalizado como prova concreta. |
| Transfer | **Parcial forte** | `Transfer/Hurwitz.lean`, `ZetaTransfer.lean`, `RH.lean` | O empacotamento final ate `zeta` e RH ja esta formalizado e compilando; o passo de Hurwitz segue como interface classica explicita. |
| Numerical | **Fechado / Suporte** | `Numerical/Constants.lean`, `Verification.lean` | Constantes default e infraestrutura numerica auxiliar ja presentes. |

---

## 5. O que ainda entra como input externo

Hoje os pontos principais ainda nao internalizados como prova Lean completa sao:

- `Transfer/Hurwitz.lean`: o passo de Hurwitz esta empacotado pela interface axiomatica `hurwitzTransferOffCriticalStrip`;
- `Bulk/ClassicalAxioms.lean`: os insumos classicos pesados do regime bulk ainda entram explicitamente como axiomas/hipoteses;
- `Bulk/FXNonZeroBulk.lean` e `Edge/FEdgeNonZero.lean`: a nao anulacao operacional nessas regioes ainda nao esta toda deduzida por prova interna concreta;
- `Finite/FiniteCertificate.lean`: o certificado finito ainda e um pacote abstrato, nao um artefato numerico totalmente auditado dentro do kernel;
- `NearAxis/Amplification.lean`: permanece mais proximo de scaffold do que de camada final fechada;
- a producao concreta de witnesses de Taylor a partir do objeto genuine real ainda nao foi amarrada de ponta a ponta.

Esse desenho e deliberado: a cadeia principal nao esconde onde a prova ainda
depende de input classico ou numerico externo.

---

## 6. Mapeamento doc → arquivo Lean

Tabela inversa principal:

| Documento | Arquivos Lean correspondentes |
|---|---|
| [c2_rota_K_rigorosamente_fechada.md](c2_rota_K_rigorosamente_fechada.md) | `Foundations/*`, `Operators/*`, `Identity/*`, `Cutoff/*`, parte do `NearAxis/*` |
| [algebra_Z_igual_zeta.md](algebra_Z_igual_zeta.md) | `Identity/C0.lean`, `Identity/C0NonZero.lean`, `Identity/FundamentalIdentity.lean` |
| [c2_prova_continuacao_Z_zeta.md](c2_prova_continuacao_Z_zeta.md) | `Identity/MeromorphicExt.lean` |
| [c2_prova_thm8_transversal.md](c2_prova_thm8_transversal.md) | `NearAxis/Transversality.lean` |
| [c2_lower_bound_transversal_taylor.md](c2_lower_bound_transversal_taylor.md) | `NearAxis/TaylorRadius.lean`, `NearAxis/GlobalBound.lean`, `NearAxis/FXNonZero.lean` |
| [c2_certificacao_bound_global.md](c2_certificacao_bound_global.md) | `NearAxis/GlobalBound.lean`, `Numerical/Constants.lean` |
| [c2_cutoff_adaptativo_quarteto.md](c2_cutoff_adaptativo_quarteto.md) | `Operators/Cutoff.lean`, `Cutoff/DecayRate.lean` |
| [c2_prova_taxa_decaimento_cutoff.md](c2_prova_taxa_decaimento_cutoff.md) | `Cutoff/DecayRate.lean` |
| [c2_quarteto_resolvente_sharpening.md](c2_quarteto_resolvente_sharpening.md) | `Bulk/Resolvent.lean`, `Bulk/QuartetSharp.lean` |
| [nota_offaxis_c2.md](nota_offaxis_c2.md) | `Operators/Branch.lean`, `Operators/BranchNormBarrier.lean` |
| [c2_operador_ramo_invariancia_t_ponte_genuine.md](c2_operador_ramo_invariancia_t_ponte_genuine.md) | `Operators/BranchToGenuine.lean` |
| [c2_bulk_offaxis_route3_tilt.md](c2_bulk_offaxis_route3_tilt.md) | `Bulk/ClassicalAxioms.lean`, `Bulk/BulkLowerBound.lean` |
| [c2_bulk_offaxis_edge_lemma.md](c2_bulk_offaxis_edge_lemma.md) | `Edge/EdgeRight.lean`, `Edge/EdgeLeft.lean`, `Edge/FEdgeNonZero.lean` |
| [c2_bulk_offaxis_glue.md](c2_bulk_offaxis_glue.md) | `Glue/*.lean`, interfaces regionais de `NearAxis/Bulk/Edge` |
| [c2_bulk_offaxis_transfer.md](c2_bulk_offaxis_transfer.md) | `Transfer/Hurwitz.lean`, `Transfer/ZetaTransfer.lean`, `Transfer/RH.lean` |
| [teorema_faixa_diadica_zero_free.md](teorema_faixa_diadica_zero_free.md) | `Finite/DyadicCoverage.lean`, `Finite/FiniteCertificate.lean` |
| [hadamard_von_mongoldt.md](hadamard_von_mongoldt.md) | usado pela interpretacao do bound global em `NearAxis/GlobalBound.lean` |
| [c2_resumo_formalizacao_lean.md](../docs/c2_resumo_formalizacao_lean.md) | snapshot de status, nao documento-fonte da prova |

Documentos fora da cadeia minima formal:

- [c2_bulk_offaxis_route2_rouche.md](../docs/c2_bulk_offaxis_route2_rouche.md): exploracao opcional, nao usada na cadeia minima atual;
- [c2_inversao_zeros_via_FFT.md](../docs/c2_inversao_zeros_via_FFT.md) e [c2_dualidade_primo_zero.md](../docs/c2_dualidade_primo_zero.md): exploracoes fora do nucleo Lean;
- [cadeia_unica.md](../docs/cadeia_unica.md) e [fechamento_unificado.md](../docs/fechamento_unificado.md): sinteses conceituais, nao camada de implementacao direta;
- variantes `_atualizada`, `_OLF` e afins: material de apoio, nao fonte canonical da arvore Lean.

---

## 7. Endpoints e APIs já expostos

Identificadores importantes ja presentes na arvore atual:

- `Glue/Decomposition.lean`:
  `offCriticalStrip`, `stripHeight`, `criticalOffset`, `nearRegion`, `bulkRegion`, `edgeRegion`, `glueCovering`, `nearRegion_mono`.
- `NearAxis/TaylorRadius.lean`:
  `taylorExclusionRadius`, `routeK_elo5_nonzero_from_taylor`, `taylorNonvanishingWitness`.
- `NearAxis/GlobalBound.lean`:
  `deltaStarLowerModel`, `routeK_thm11_deltaStar_lower_bound_logSq`.
- `NearAxis/FXNonZero.lean`:
  `nearRegionEventuallyNonvanishing_of_taylorWitness`, `nearRegionEventuallyNonvanishing_of_ge_deltaStarLowerModel`, `nearRegionEventuallyNonvanishing_of_taylorWitness_of_ge_deltaStarLowerModel`.
- `Finite/FiniteCertificate.lean`:
  `DefaultFiniteAndGlueData`, `DefaultGlobalBoundData`, `cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultData`, `cutoffFamilyEventuallyNonvanishingOnOffCriticalStrip_of_defaultGlobalBoundData`.
- `Transfer/ZetaTransfer.lean`:
  `riemannZeta_nonvanishing_offCriticalStrip_of_defaultData`, `riemannZeta_nonvanishing_offCriticalStrip_of_defaultGlobalBoundData`, `routeK_default_offaxis_riemannZeta_nonvanishing`, `routeK_default_globalBound_offaxis_riemannZeta_nonvanishing`.
- `Transfer/RH.lean`:
  `RiemannHypothesisC2`, `riemannHypothesisC2_of_defaultData`, `riemannHypothesisC2_of_defaultGlobalBoundData`, `routeK_default_chain_RH`, `routeK_default_globalBound_chain_RH`.

Esses nomes sao hoje a API arquitetural mais util para amarrar novos passos
sem reabrir a cadeia inteira.

---

## 8. Build, toolchain e CI

Configuracao real atual:

- `lean-toolchain`: `leanprover/lean4:v4.29.1`
- `lakefile.toml`: pacote `LeanC2`, `defaultTargets = ["LeanC2"]`
- Mathlib pinned em `v4.29.1`

Build local:

```bash
cd /home/thlinux/C2_Hipotese_De_Riemann/Lean
lake exe cache get
lake build
```

Estado atual:

- a arvore Lean inteira ja fecha em `lake build`;
- o arquivo raiz `LeanC2.lean` ja importa `Cutoff.Residue`, `Finite.DyadicCoverage`, `Numerical.Constants` e `Numerical.Verification`;
- ainda nao existe `.github/workflows/` no repositorio Lean.

Recomendacao pratica de proximo passo para infraestrutura: adicionar um workflow
minimo de CI que rode `lake exe cache get && lake build` e um audit opcional de
axiomas para os endpoints finais de `Transfer/RH.lean`.

---

## 9. Convenções de manutenção

Convencoes que continuam valendo e refletem o estado atual do repo:

- manter a separacao entre prova interna e interface classica explicitamente no tipo dos teoremas;
- evitar `sorry` na cadeia principal;
- preferir docstrings curtas com referencia a nota-fonte relevante;
- usar nomes Lean/Mathlib-style ja estabilizados na base, em vez de placeholders de roadmap;
- preservar os pacotes default `DefaultFiniteAndGlueData` e `DefaultGlobalBoundData` como pontos de entrada canonicos;
- quando esta nota for atualizada, sincronizar tambem a copia em `Lean/c2_lean_architecture.md`.

---

## 10. Próximos passos realistas

1. Internalizar a producao concreta de witnesses de Taylor no near-axis, reduzindo a dependencia de interfaces abstratas.
2. Substituir as interfaces finais de `FXNonZeroBulk.lean` e `FEdgeNonZero.lean` por camadas mais concretas de prova.
3. Importar o certificado finito como artefato auditavel, com log e hash reprodutivel.
4. Auditar `#print axioms` para os endpoints finais de `Transfer/ZetaTransfer.lean` e `Transfer/RH.lean`.
5. Adicionar CI basico ao repositorio Lean.
6. Continuar reduzindo a distancia entre a nota arquitetural e a API real exposta pelos arquivos `LeanC2/*.lean`.

---

## 11. Referências externas

| Referência | Uso |
|---|---|
| Ford, K. *Vinogradov's integral and bounds for ζ*. Proc LMS 85 (2002). | Bounds efetivos tipo V-K |
| Titchmarsh, E.C. *The Theory of the Riemann Zeta-Function*, 2nd ed. (Heath-Brown), Oxford 1986. | Equacao funcional, Phragmen-Lindelof, analytic continuation |
| Iwaniec & Kowalski, *Analytic Number Theory*, AMS 2004. | Hadamard, estimativas de densidade, pano de fundo analitico |
| Edwards, H.M. *Riemann's Zeta Function*. | Referencia historica e estrutural |
| Mossinghoff & Trudgian, *Nonnegative trigonometric polynomials and a zero-free region for ζ*, J. Number Theory (2015). | Refinamentos de zero-free region |

---

## 12. Status resumido

| Item | Estado atual |
|---|---|
| Repositorio Lean em `Lean/` | ✅ |
| Toolchain pinned | ✅ Lean `v4.29.1`, Mathlib `v4.29.1` |
| `LeanC2.lean` reexporta a arvore atual | ✅ |
| `lake build` da arvore toda | ✅ |
| Endpoint default ate `ζ ≠ 0` off-axis | ✅ |
| Endpoint default ate RH em forma C2 | ✅ |
| Bulk e Edge 100% internalizados | ❌ ainda parciais/interface |
| Certificado finito internalizado no kernel | ❌ ainda abstrato |
| CI GitHub Actions configurado | ❌ ainda nao |

Leitura complementar imediata: [c2_resumo_formalizacao_lean.md](../docs/c2_resumo_formalizacao_lean.md).

