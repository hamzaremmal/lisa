package lisa.ol

import lisa.kernel.proof.RunningTheory

object OrthologicWithAxiomsLibrary extends lisa.prooflib.Library {

  override val theory = new RunningTheory

  // ==============================================================================================
  // ======================================== ORTHOLATTICE ========================================
  // ==============================================================================================

  val hyp = Theorem(ortholattice(S, leq, meet, join, neg2) /\ (x ∈ S) |- (x leq x)) {
    assume(ortholattice(S, leq, meet, join, neg2))
    have(∀(x, (x ∈ S) ==> (x leq x))) by Tautology.from(ortholattice.definition, reflexive2.definition)
    thenHave(thesis) by InstantiateForall(x)
  }

}
