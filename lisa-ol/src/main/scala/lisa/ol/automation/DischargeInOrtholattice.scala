package lisa.ol
package automation

import lisa.fol.FOL.*
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.ProofTacticLib.ProofTactic

import lisa.automation.Tautology

object DischargeInOrtholattice extends ProofTactic:

  def withParameters(using lib: OrthologicWithAxiomsLibrary, proof: lib.Proof)
                    (td: Term*)
                    (premise: proof.Fact): proof.ProofTacticJudgement =
    import lib.{in, ∈, U, inU, isO, have, andThen}
    val premiseSeq = proof.sequentOfFact(premise)
    val bot = premiseSeq.removeAllLeft(inU(td*).toSet)
    val termsInU = bot.left.collect { case in(x1, `U`) => x1 }

    val toDischarge = premiseSeq.left.collect {
      case in(x1, `U`) if !termsInU.contains(x1) => x1
    }

    val premises = isO +: inU(termsInU.toSeq *)
    TacticSubproof:
      if toDischarge.isEmpty then
        have(bot) by Tautology.from(premise) // FIX
      else
        val fs = toDischarge.toSeq.map: xi =>
          have(premises |- xi ∈ U) by ElementInOrtholattice.withParameters(xi)
        have(premiseSeq) by Tautology.from(premise) // FIX
        andThen(Discharge(fs *))
  end withParameters

end DischargeInOrtholattice
