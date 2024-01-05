package lisa.ol
package automation

import lisa.automation.Tautology
import lisa.fol.FOL.*
import lisa.prooflib.ProofTacticLib.ProofTactic
import lisa.prooflib.BasicStepTactic.*
import lisa.prooflib.SimpleDeducedSteps.*

object ElementInOrtholattice extends ProofTactic:
  
  // NOTE: To force using this tactic with the OrthologicWithAxiomsLibrary, we summon `OrthologicWithAxiomsLibrary` instead of `Library`
  def withParameters(using lib: OrthologicWithAxiomsLibrary, proof: lib.Proof)(term: Term)(bot: Sequent) : proof.ProofTacticJudgement =
    import lib.{unorderedPair, app, ∈, `0`, `1`, not, U, n, u, x, y, have, lastStep}
    object Singleton:
      def unapply(t: Term): Option[Term] = t match
        case unorderedPair(x1, x2) if x1 == x2 => Some(x1)
        case _ => None

    object Pair:
      def unapply(t: Term): Option[(Term, Term)] = t match
        case unorderedPair(unorderedPair(x1, y1), Singleton(x2)) if x1 == x2 => Some((x1, y1))
        case _ => None
    val (meet, join) = (n, u)
    term match
      case `0` =>
        TacticSubproof:
          have(bot) by Tautology.from(lib.ortholattice.definition, lib.zeroInOrtholattice)
      case `1` =>
        TacticSubproof:
          have(bot) by Tautology.from(lib.ortholattice.definition, lib.oneInOrtholattice)
      case app(`not`, x1) =>
        withParameters(x1)(bot.left |- x1 ∈ U) andThen2 { lastStep =>
          have(bot) by Cut.withParameters(x1 ∈ U)(lastStep, lib.negationIsClosed of (x := x1))
        }
      case app(`meet`, Pair(left, right)) =>
        withParameters(left)(bot.left |- left ∈ U) andThen { s1 =>
          withParameters(right)(bot.left |- right ∈ U) andThen2 { s2 =>
            have(bot.left |- left ∈ U /\ right ∈ U) by RightAnd(s1, s2)
            have(bot) by Cut(lastStep, lib.meetIsClosed of(x := left, y := right))
          }
        }
      case app(`join`, Pair(left, right)) =>
        withParameters(left)(bot.left |- left ∈ U) andThen { s1 =>
          withParameters(right)(bot.left |- right ∈ U) andThen2 { s2 =>
            have(bot.left |- left ∈ U /\ right ∈ U) by RightAnd(s1, s2)
            have(bot) by Cut(lastStep, lib.joinIsClosed of(x := left, y := right))
          }
        }
      case x if bot.left contains x ∈ U =>
        TacticSubproof:
          have(x ∈ U |- x ∈ U) by Restate
          have(bot) by Weakening(lastStep)
      case x =>
        proof.InvalidProofTactic(s"Could not prove $x ∈ $U. Make sure that your sequent has the following form : `(ortholattice, $x ∈ $U, ...) |- ...`")
  end withParameters

end ElementInOrtholattice
