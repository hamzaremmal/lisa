package lisa.ol

import lisa.fol.FOLHelpers.variable

object OLExample extends lisa.ol.Main:

  val x = variable
  val y = variable
  val z = variable
  val p = variable
  val q = variable
  val u = variable

  // ==============================================================================================
  // ===================================== AXIOM CHECKING ========================================
  // ==============================================================================================

  val reflexitivity = Theorem(x <= x) {
    have(thesis) by Tautology.from(P1 of (y := x))
  }

  val check_antisymmetry = Theorem(((x <= y) /\ (y <= x)) |- (x === y)) {
    have(thesis) by Tautology.from(antisymmetry)
  }

  val check_P3 = Theorem(x <= 1) {
    have(thesis) by Tautology.from(P_3)
  }

  // ==============================================================================================
  // =================================== OL WITHOUT AXIOMS ========================================
  // ==============================================================================================

  val section_1_2_without_axiom = Theorem((x n (!x u u)) <= u |- ()) {
    sorry
  }

  val section_1_2_with_axiom = Theorem((x n (!x u u)) <= u) {
    sorry
  }
