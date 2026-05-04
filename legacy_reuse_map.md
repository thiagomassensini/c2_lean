# Mapa de Reaproveitamento do Legado

Este arquivo resume o que vale reaproveitar de `Antigo_Lean_C2/` na nova arvore `LeanC2/`.

## Prioridade alta

| Legado | Novo destino | Observacao |
|---|---|---|
| `Barrier.lean` | `LeanC2/Operators/Branch.lean`, `LeanC2/Operators/BranchNormBarrier.lean` | Formula fechada da massa dominante e barreira em `sigma = 1/2`. |
| `OperatorNorm.lean` | `LeanC2/Operators/Branch.lean`, `LeanC2/Operators/BranchNormBarrier.lean`, `LeanC2/Operators/BranchToGenuine.lean` | Ja tem os nomes de teoremas mais proximos da arquitetura nova. |
| `Normalization.lean` | `LeanC2/Identity/C0.lean`, `LeanC2/Identity/C0NonZero.lean` | Melhor ponto de partida para Thm 14. |
| `Identity.lean` | `LeanC2/Identity/FundamentalIdentity.lean`, `LeanC2/Identity/MeromorphicExt.lean` | Ja separa Thm 13 e Thm 17 em forma reaproveitavel. |
| `Tilt.lean` | `LeanC2/Foundations/Tilt.lean`, `LeanC2/NearAxis/Transversality.lean` | Contem Thm 2, Thm 5 e os lemas abstratos de transversalidade. |
| `TiltConvexity.lean` | `LeanC2/Foundations/Tilt.lean` | Bom para limpar as provas de convexidade e manter `Tilt.lean` menor. |
| `Continuation.lean` | `LeanC2/Transfer/ZetaTransfer.lean`, `LeanC2/Transfer/RH.lean` | Serve como semente da etapa final de transferencia. |

## Prioridade media

| Legado | Novo destino | Observacao |
|---|---|---|
| `Tree.lean` | `LeanC2/Foundations/DyadicArith.lean` | Estrutura de enderecos e suporte de linhas. |
| `GlobalDecomposition.lean` | `LeanC2/Foundations/DyadicArith.lean` ou modulo auxiliar futuro | Bom material, mas ainda mais largo que o minimo necessario. |
| `CutoffDecay.lean` | `LeanC2/Cutoff/DecayRate.lean`, `LeanC2/NearAxis/FXNonZero.lean` | Ja empacota bem o `O(1/X)` e a parte de exclusao. |
| `Chain.lean` | `LeanC2/Operators/BranchToGenuine.lean`, `LeanC2/Transfer/RH.lean` | Mais util como mapa conceitual do que como arquivo para copiar direto. |

## Prioridade baixa ou opcional

| Legado | Novo destino | Observacao |
|---|---|---|
| `Pushforward.lean` | `LeanC2/Operators/Genuine.lean` ou modulo futuro opcional | Muito rico, mas maior que o necessario para levantar o scaffold minimo. |
| `Composite.lean` | A decidir depois | Parece mais camada de empacotamento do projeto antigo. |

## Ordem pratica de port

1. `Normalization.lean` -> `Identity/C0.lean` e `Identity/C0NonZero.lean`
2. `Identity.lean` -> `Identity/FundamentalIdentity.lean` e `Identity/MeromorphicExt.lean`
3. `Barrier.lean` + `OperatorNorm.lean` -> `Operators/Branch.lean` e `Operators/BranchNormBarrier.lean`
4. `TiltConvexity.lean` + `Tilt.lean` -> `Foundations/Tilt.lean`
5. Parte abstrata de `Tilt.lean` -> `NearAxis/Transversality.lean`
6. `CutoffDecay.lean` -> camada `Cutoff/`
7. `Continuation.lean` -> camada `Transfer/`

## Regra de migracao

- Nao copiar o projeto antigo em bloco.
- Migrar por teorema, ajustando nomes e imports ao layout novo.
- Cada teorema migrado deve manter a referencia da nota papel correspondente.
- Quando um arquivo antigo mistura varias camadas, quebrar no destino antes de portar a prova.
