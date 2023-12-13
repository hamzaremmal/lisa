package lisa.ol

import lisa.fol.FOLHelpers.variable
import lisa.fol.FOL.|-
import lisa.ol.OLExample.x

object OLExample extends lisa.ol.Main:

  val x = variable
  val y = variable
  val z = variable
  val p = variable
  val q = variable
  val u = variable

  val axiom1 = Axiom((x n (!x u u)) === 1)

  // ==============================================================================================
  // ==================================== TEST AXIOM TACTIC =======================================
  // ==============================================================================================

  val check_axiom_1 = Theorem(() |- ((x n (!x u u)) === 1)) {
    have(thesis) by Axiom
  }

  val check_axiom_2 = Theorem((x n (!x u u)) === 1) {
    axiom
  }
