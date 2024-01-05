package lisa.ol
package tests

import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.SimpleDeducedSteps.*

object DischargeInOrtholatticeTest extends OrthologicWithAxiomsMain with OrthologicWithAxiomsLibrary:

  val test_01 = Theorem((isO, x ∈ U) |- !x ∈ U):
    have(!x ∈ U |- !x ∈ U) by Restate
    have((isO, x ∈ U, !x ∈ U) |- !x ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters(!x)(s)
  end test_01

  val test_02 = Theorem((isO, x ∈ U, y ∈ U) |- (x n y) ∈ U):
    have((x n y) ∈ U |- (x n y) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, (x n y) ∈ U) |- (x n y) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters(x n y)(s)
  end test_02

  val test_03 = Theorem((isO, x ∈ U, y ∈ U) |- (x u y) ∈ U):
    have((x u y) ∈ U |- (x u y) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, (x u y) ∈ U) |- (x u y) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters(x u y)(s)
  end test_03

  val test_04 = Theorem((isO, x ∈ U, y ∈ U) |- (!x n y) ∈ U):
    have((!x n y) ∈ U |- (!x n y) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, (!x n y) ∈ U) |- (!x n y) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters(!x n y)(s)
  end test_04

  val test_05 = Theorem((isO, x ∈ U, y ∈ U) |- (!x u y) ∈ U):
    have((!x u y) ∈ U |- (!x u y) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, (!x u y) ∈ U) |- (!x u y) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters(!x u y)(s)
  end test_05

  val test_06 = Theorem((isO, x ∈ U, y ∈ U) |- (x n !y) ∈ U):
    have((x n !y) ∈ U |- (x n !y) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, (x n !y) ∈ U) |- (x n !y) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters(x n !y)(s)
  end test_06

  val test_07 = Theorem((isO, x ∈ U, y ∈ U) |- (x u !y) ∈ U):
    have((x u !y) ∈ U |- (x u !y) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, (x u !y) ∈ U) |- (x u !y) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters(x u !y)(s)
  end test_07

  val test_08 = Theorem((isO, x ∈ U, y ∈ U, z ∈ U) |- ((x n y) n z) ∈ U):
    have(((x n y) n z) ∈ U |- ((x n y) n z) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, z ∈ U, ((x n y) n z) ∈ U) |- ((x n y) n z) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters((x n y) n z)(s)
  end test_08

  val test_09 = Theorem((isO, x ∈ U, y ∈ U, z ∈ U) |- ((x n y) u z) ∈ U):
    have(((x n y) u z) ∈ U |- ((x n y) u z) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, z ∈ U, ((x n y) u z) ∈ U) |- ((x n y) u z) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters((x n y) u z)(s)
  end test_09

  val test_10 = Theorem((isO, x ∈ U, y ∈ U, z ∈ U) |- ((x u y) n z) ∈ U):
    have(((x u y) n z) ∈ U |- ((x u y) n z) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, z ∈ U, ((x u y) n z) ∈ U) |- ((x u y) n z) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters((x u y) n z)(s)
  end test_10

  val test_11 = Theorem((isO, x ∈ U, y ∈ U, z ∈ U) |- ((x u y) u z) ∈ U):
    have(((x u y) u z) ∈ U |- ((x u y) u z) ∈ U) by Restate
    have((isO, x ∈ U, y ∈ U, z ∈ U, ((x u y) u z) ∈ U) |- ((x u y) u z) ∈ U) by Weakening(lastStep)
    andThen: s =>
      DischargeInOrtholattice.withParameters((x u y) u z)(s)
  end test_11

end DischargeInOrtholatticeTest
