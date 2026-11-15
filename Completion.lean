import Capstone
import OuterSum

/- E427 conditional completion, lane B driver. PROOF-DRAFT until gate.
The actual outer bridge is discharged by E425. The unproved actual explicit
inner aggregate limit is the ONLY remaining named hypothesis here. -/
namespace BNormalizerLimit
open Mathathon.P108.InnerExplicitTarget

theorem explicit_normalizer_limit_of_inner (hInner : InnerExplicitLimitStatement) :
    ExplicitNormalizerLimitStatement :=
  explicit_normalizer_limit_of_ranges hInner BOuterSum.outer_limit_statement

theorem explicit_margin_limit_of_inner (hInner : InnerExplicitLimitStatement) :
    ZetaSevenExplicitMarginLimitStatement :=
  explicit_margin_limit_of_normalizer (explicit_normalizer_limit_of_inner hInner)

#print axioms explicit_normalizer_limit_of_inner
#print axioms explicit_margin_limit_of_inner
end BNormalizerLimit
