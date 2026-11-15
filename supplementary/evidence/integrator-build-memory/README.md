# Peak memory of the submitted Lean project, module by module

*Integrator (Claude Fable 5.2, Claude Code on [team machine]), Sun 00:20 PT. COMPUTED on [team machine] (macOS, 64 GB, 18 cores) in a clean clone of [team handle]/mathathon-108 at commit 5b59e442aedd4d69bdf81d05149d729df7331e13, after a full build: each module re-elaborated alone with `/usr/bin/time -l lake env lean <file>`; "peak" is the maximum resident set size that command prints.*

**Why.** The GitHub workflow of the judged repository (Lean Action CI, a standard `ubuntu-latest` runner) failed in its build step after 25 minutes on this commit (run 43690003319) and the job then hung; its log is not available. The same commit builds here in 351 s. The organizers' automated check also builds on another machine.

**First nine modules (the slowest of the local build):** `peak_memory_first9.txt`.

| Module | Peak | Time alone |
|---|---|---|
| `UValidation` (one `decide +kernel` over all the U rows of the field certificate) | **25.91 GB** | 102 s |
| `VValidation` (the same for the V rows and the critical data) | 8.63 GB | 15 s |
| `Mathathon/P108/DetG0` | 8.61 GB | 35 s |
| `NumericProof/Atan000` | 6.25 GB | 7 s |
| `Apery/ZeroMass` (upstream's file) | 5.56 GB | 10 s |
| `LeanWitness/ClassLoss` | 5.54 GB | 23 s |
| `Mathathon/P108/DeltaEq/HankelCheck` | 4.94 GB | 14 s |
| `Mathathon/P108/OuterValues` | 3.58 GB | 31 s |
| `Mathathon/P108/DeltaEq/Pt/Points` | 3.13 GB | 115 s |

**Reading (HEURISTIC until the runner's log is seen):** a module that needs 26 GB cannot build on a small runner, and lake runs several modules at once. This is the likely cause of the failed run, and a risk for the organizers' build.

A second batch (the next sixty modules by build time) is being measured; its result is added to this folder.

## Correction and calibration (Sun 00:27 PT)

**The figures above include a baseline that is not a problem.** A file that contains only `import Mathlib` shows a peak of **5.42 GB** by this measure (the imported library files are memory-mapped and counted); a file with only `import FieldData` shows 5.43 GB. All sixty modules of the second batch (`peak_memory_next60.txt`) lie between 5.5 and 6.1 GB, that is, at the baseline. So:

| Module | Peak | Above the baseline |
|---|---|---|
| `UValidation` | 25.91 GB | **about 20.5 GB: the one real outlier** |
| `VValidation` | 8.63 GB | about 3.2 GB |
| `Mathathon/P108/DetG0` | 8.61 GB | about 3.2 GB |
| `NumericProof/Atan000` and its siblings, `Apery/ZeroMass`, `LeanWitness/ClassLoss` | 5.5 to 6.3 GB | under 1 GB: not a concern |

The earlier target "no module above 4 GB" was wrong, because no module that imports Mathlib can be below 5.4 GB by this measure. **The target is: no module more than about 1 GB above the baseline (under 6.5 GB as measured here).** That means splitting `all_u_ok` (essential), and `all_v_ok`, `critical_ok` and the check in `DetG0` (advisable). The modules of upstream's project and the NumericProof blocks need no change.

## What GitHub says about the failed run (Sun 00:46 PT)

Run 43690003319 (commit 5b59e442) is now closed as a failure. Its job carries GitHub's annotation: "The hosted runner lost communication with the server. Anything in your workflow that terminates the runner process, starves it for CPU/Memory, or blocks its network access can cause this error." No log was kept for the job. This agrees with the measurement above (one module needing about 20 GB above the baseline) and is not a Lean error message. Lane C's fix (E616) splits that check; a green run on the fixed commit is the test.

## The fixed commit builds on GitHub's runner (Sun 02:05 PT)

Run 43700182132 of the judged repository's workflow built commit 5eb1923b1c499323e1a4eae405eea3979362def9 (lane C's E616: the U and V checks of the field certificate split into blocks) on a standard `ubuntu-latest` runner: all steps successful, the build step from 09:38:06 to 10:04:15 UTC (26 minutes). COMPUTED (a build on one hosted runner; it runs the default target, not the team's gate and not the Comparator). The run of the earlier commit 5b59e442 on the same kind of runner had failed with "the hosted runner lost communication with the server". On [team machine]: `UValidation` 5.49 GB peak (25.91 GB before), `VValidation` 5.47 GB (8.63 before), a block module 6.10 GB, baseline 5.43 GB; clean build 400 s; final gate 43/43.

## Why the further split of DetG0 (E617) is not submitted (Sun 07:59 PT)

Lane C split the kernel check of the determinant audit (`DetG0`, 8.6 GB peak alone) into 36 block modules, each under 6.5 GB alone. On [team machine] (18 cores, 64 GB) a plain `lake build` compiles 18 of them at once: COMPUTED on this machine, three attempts: physical memory 63 GB used with 33 GB in the compressor and 25 GB of swap, 55 percent system time, no progress for 40 minutes. After stopping it, 40 GB were free at once. Built eight blocks at a time (five `lake build` calls of about 30 s each), the blocks finish and the whole project then builds in 377 s with no error. Reading: each block needs about 2.5 to 3 GB of memory of its own while it runs, so the split trades one module of 8.6 GB for many that become ready together; on a machine with many cores and moderate memory that is worse. The submitted commit is therefore `b14f8c3b` (DetG0 unsplit), which built green on a hosted Linux runner (run 43730663696) and from clean on [team machine] (508 s).
