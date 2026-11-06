module

public import Konig.ConstructionLimit
public import Konig.CandidateFormula

@[expose] public section

namespace Konig

theorem constant_eq_one : constant = 1 :=
  Construction.constant_eq_one_of_candidate_formula
    (fun _ a s hb r => Construction.candidate_formula a s hb r)

end Konig
