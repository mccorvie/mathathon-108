import Bounds
import Discontinuities
import Inversion
import Integrability
/- E426 Codex inner_regularity. PROOF-DRAFT combined actual-model targets. -/
namespace BInnerLimit

theorem regularity_and_inversion :
    BoundedStatement ∧ FiniteDiscontinuitiesStatement ∧ InversionStatement :=
  ⟨bounded_statement, finite_discontinuities_statement, inversion_statement⟩

#print axioms regularity_and_inversion
end BInnerLimit
