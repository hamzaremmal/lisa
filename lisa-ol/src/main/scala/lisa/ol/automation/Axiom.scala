package lisa.ol.automation

import lisa.fol.FOL as F
import lisa.utils.K
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.{ProofTactic, ProofSequentTactic}

object Axiom extends ProofTactic with ProofSequentTactic {

  override def apply(using lib: Library, proof: lib.Proof)(bot: F.Sequent): proof.ProofTacticJudgement =
    val botK = bot.underlying
    val pivot = botK.left.union(botK.right)
    lib.theory.getAxiom(pivot.head) match
      case Some(axiom) =>
        // TODO HR : Add REstate and weakening
        proof.ValidProofTactic(
          bot,
          Seq(),
          Seq(lib.AXIOM(axiom, bot.right.head, axiom.name))
        )
      case None => proof.InvalidProofTactic("The desired formula is not an axiom of the theory")

}
