# Comparator for the zeta(5) statement

Run from either repository root:

```bash
./verify-comparator.sh
```

The research repository's runner selects its submitted v4.35.0 project at
`problems/108-zeta-odd-autopsy/evidence/L-merge/project/`. In the standalone
`mathathon-108` repository it selects the root project. The research root's
legacy toolchain is not changed.

`comparator.json` selects the independently compiled modules
`Mathathon.Zeta5Comparator.Challenge` and `Mathathon.Zeta5Comparator.Solution`, and the declaration
`RiemannZetaValues.irrational_five`:

```lean
∃ x, Irrational x ∧ riemannZeta 5 = x
```

**CITED:** this statement is the Formal Conjectures benchmark at commit
`2db01438fda960163f58ff2c2385b52e53f56dd2`; its source is linked in the challenge.
The solution delegates to `CCertificateSplit.irrational_five`, the project's
existing re-derivation of Fauzan's theorem, with its original credits intact.

The challenge imports only Mathlib. Its intentional `sorry` is the trusted
benchmark hole; it is not imported into the solution or the default build.
The solution contains no such hole. The two modules use the existing Mathathon library and have no aggregate
module that imports both definitions. No Lake configuration change is required.

Lean v4.35.0 includes `lake comparator`. Its successful verdict checks statement
identity, the configured axiom whitelist (`propext`, `Quot.sound`,
`Classical.choice`), and Lean kernel acceptance. See the installed
`lake help comparator` and the [Lean Comparator documentation](https://github.com/leanprover/comparator).
This configuration selects the Lean kernel; it does not request additional kernels.

The default command requires Linux with working `bubblewrap`; the GitHub workflow
installs it. For local verification of these trusted sources on macOS, explicitly use:

```bash
./verify-comparator.sh --inadvisably-no-sandbox
```

That local run has no sandbox isolation. A recorded local verdict must identify
that mode, and is not evidence that the Linux sandboxed CI has run.
