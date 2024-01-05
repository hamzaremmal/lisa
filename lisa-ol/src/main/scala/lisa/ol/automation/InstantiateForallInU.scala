package lisa.ol
package automation

import lisa.fol.FOL.*
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.prooflib.SimpleDeducedSteps.*
import lisa.prooflib.BasicStepTactic.*

object InstantiateForallInU extends ProofTactic:

  def apply(using lib: OrthologicWithAxiomsLibrary, proof: lib.Proof)
           (xs: Variable*)(premise: proof.Fact)(bot: Sequent): proof.ProofTacticJudgement =
    import lib.{inU, U, assume, have, thenHave, lastStep, in}
    val premiseSeq = proof.sequentOfFact(premise)

    if bot.right.size != 1 then return proof.InvalidProofTactic("") // TODO
    if premiseSeq.right.size != 1 then return proof.InvalidProofTactic("") // TODO
    if !(inU(xs *).toSet subsetOf premiseSeq.left) then return proof.InvalidProofTactic("") // TODO

    TacticSubproof:
      assume(premiseSeq.left.toSeq *)
      have(premiseSeq) by Restate.from(premise)

      for xi <- xs do
        lastStep.bot.right.head match
          case BinderFormula(Forall, `xi`, phi1@AppliedConnector(Implies, Seq(in(`xi`, `U`), phi2))) =>
            //            case F.BinderFormula(F.Forall, `xi`, phiBody) =>
            //              println("phi1: " + phi1); println("phi2: " + phi2)
            thenHave(phi1) by InstantiateForall(xi)
            thenHave(phi2) by Rewrite // TODO err msgs

          case _ => return proof.InvalidProofTactic("") // RN
      thenHave(bot) by Rewrite // NOTE can undo RightImplies
  end apply

end InstantiateForallInU
