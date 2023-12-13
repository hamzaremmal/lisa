package lisa.ol

import lisa.prooflib.ProofsHelpers

/**
 * ???
 */
trait OLProofHelpers extends ProofsHelpers {
  lib: OrthologicLibrary =>

  /**
   * ???
   * @param proof ???
   * @return ???
   */
  final inline def axiom(using proof: lib.Proof): proof.ProofStep =
    have(thesis) by automation.Axiom

}
