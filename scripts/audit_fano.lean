module

import RequestProject.TheoremA.Fano
import Solution

/-!
Audit for Theorem A of embedding_fpn (3).pdf.
Run: lake build RequestProject Challenge Solution
     lake env lean scripts/audit_fano.lean

The commands below print the statement, finite construction, and theorem types
for inspection. Palomar performs the separate proof comparison and kernel
checks for the configured Challenge/Solution pair.
-/

set_option pp.universes true

#print TheoremA.IsFP
#print TheoremA.TheoremAStatement
#print FanoTriples.triples
#print FanoTriples.pointTriple
#print FanoTriples.lineTriple
#print FanoTriples.nu
#print TheoremA.theoremA_of_ingredients

set_option pp.explicit true in
#check @FanoTriples.proposition_3_2
set_option pp.explicit true in
#check @TheoremA.Fano.universalFP2
set_option pp.explicit true in
#check @TheoremA.Fano.universalFP
set_option pp.explicit true in
#check @TheoremA.Fano.theoremA
set_option pp.explicit true in
#check @TheoremA.theoremA
set_option pp.explicit true in
#check @TheoremA.palomarStatement

#print axioms TheoremA.palomarStatement
