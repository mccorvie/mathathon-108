# E311 human statement supplement

LEAN-CHECKED; no human verdict. Read the base sheet ../L-human-check/SHEET.md and E310 supplement first. The raw definitions remain separate.

## AperyS.AssemblyTarget.local_valuation_sharp

```lean
@AperyS.AssemblyTarget.local_valuation_sharp : ∀ {p : ℕ} [Fact (Nat.Prime p)] (s ν K N M : ℕ)
  (L : AperyS.AssemblyTarget.Allocations),
  Odd s →
    3 ≤ s →
      2 ≤ ν →
        N < K →
          2 * K ≤ AperyS.AssemblyTarget.degreeBound s ν K N →
            AperyS.GV p (AperyS.FS s ν K N (K - N)) ↑(AperyS.AssemblyTarget.LpSharp s ν K N M p L)
```
## AperyS.AssemblyTarget.normalization_sharp_statement

```lean
AperyS.AssemblyTarget.normalization_sharp_statement : AperyS.AssemblyTarget.SharpNormalizationStatement
```
## AperyS.AssemblyTarget.normalizerSharp_pos

```lean
AperyS.AssemblyTarget.normalizerSharp_pos : ∀ (s ν K N M : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  0 < AperyS.AssemblyTarget.normalizerSharp s ν K N M L
```
## AperyS.AssemblyTarget.normalizerSharp_le_raw

```lean
AperyS.AssemblyTarget.normalizerSharp_le_raw : ∀ (s ν K N M : ℕ) (L : AperyS.AssemblyTarget.Allocations),
  AperyS.AssemblyTarget.normalizerSharp s ν K N M L ≤ AperyS.AssemblyTarget.normalizer s ν K N M L
```

## Definition LpSharp

```lean
def LpSharp (s ν K N M p : ℕ) (L : Allocations) : ℤ := by
  classical
  exact if p * M ≤ K then Lsmall s ν K N p
  else if 3 * p ≤ K then
    if InnerOK s ν K N p L then vSK ν K N p + ⌊2 * WI s ν K N p L⌋
    else Lsmall s ν K N p
  else if OuterOK s K N p then vSK ν K N p + ⌊WOsharp s ν K N p⌋
  else Lsmall s ν K N p
```

## Definition normalizerSharp

```lean
def normalizerSharp (s ν K N M : ℕ) (L : Allocations) : ℚ :=
  ∏ p ∈ (range (primeBound s K N + 1)).filter Nat.Prime,
    (p : ℚ) ^ (-LpSharp s ν K N M p L)
```

## Definition SharpNormalizationStatement

```lean
def SharpNormalizationStatement : Prop :=
  ∀ (s ν K N M : ℕ) (L : Allocations),
    Odd s → 3 ≤ s → Even ν → 2 ≤ ν → N < K → 1 ≤ M →
    6 * N ≤ K → K + (ν - 2) * N ≤ ((s - 1) / 2) * K →
    2 * K ≤ degreeBound s ν K N →
    ∃ Q : ℤ[X], Q.map (Int.castRingHom ℚ) =
      C (normalizerSharp s ν K N M L) * FS s ν K N (K - N)
```

Yes/no: Are all approved raw hypotheses retained? Does only the selected outer branch change? Is that correction exactly min(raw rank,exact zero count)? Does the target lift the same FS into integer coefficients? Is positivity and comparison with the raw normalizer proved separately? No asymptotic/irrationality claim is included. Record a verdict per declaration on BOARD.md.
