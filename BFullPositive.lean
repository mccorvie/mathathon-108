-- Ready for the cached unified project; NOT claimed built in this probe.
-- Adapt import names only when the unified project renamed these modules.
import Final
import Margin

namespace BFullBridge
open Mathathon.P108.InnerExplicitTarget

theorem zeta_seven_explicit_margin_positive_statement :
    ZetaSevenExplicitMarginPositiveStatement :=
  BNormalizerMargin.explicit_margin_positive explicit_normalizer_limit_statement

#print axioms zeta_seven_explicit_margin_positive_statement
end BFullBridge
