package lisa.utils
import lisa.kernel.fol.FOL
import lisa.kernel.proof.RunningTheoryJudgement
import lisa.kernel.proof.RunningTheoryJudgement.InvalidJustification
import lisa.kernel.proof.SCProof
import lisa.utils.Helpers.repr
import lisa.utils.tactics.ProofTacticLib.ProofTactic

import java.io.File

abstract class LisaException(errorMessage: String)(using val line: sourcecode.Line, val file: sourcecode.File) extends Exception(errorMessage) {
  def showError: String
}
object LisaException {
  case class InvalidKernelJustificationComputation(errorMessage: String, underlying: RunningTheoryJudgement.InvalidJustification[?], proof: Option[Library#Proof])(using
      sourcecode.Line,
      sourcecode.File
  ) extends LisaException(errorMessage) {
    def showError: String = "Construction of proof succedded, but the resulting proof or definition has been reported to be faulty. This may be due to an internal bug.\n" +
      "The resulting faulty event is:\n" +
      s"$underlying.message\n${underlying.error match {
          case Some(judgement) => FOLPrinter.prettySCProof(judgement)
          case None => ""
        }}"
  }

  case class UnexpectedProofTacticFailureException(failure: Library#Proof#InvalidProofTactic, errorMessage: String)(using sourcecode.Line, sourcecode.File) extends LisaException(errorMessage) {
    def showError: String = "A proof tactic used in another proof tactic returned an unexpected error. This may indicate an implementation error in either of the two tactics.\n" +
      "Status of the proof at time of the error is:" +
      ProofPrinter.prettyProof(failure.proof)
  }
  /*
  class ProofStatusException(errorMessage: String)(using sourcecode.Line, sourcecode.File) extends LisaException(errorMessage){
    def showError: String = ""
  }*/

  class ParsingException(parsedString: String, errorMessage: String) extends LisaException(errorMessage) {
    def showError: String = ""
  }

  class InvalidIdentifierException(identifier: String, errorMessage: String) extends LisaException(errorMessage) {
    def showError: String = s"$identifier is not a valid string. " + errorMessage
  }
}

/**
 * Error made by the user, should be "explained"
 */
abstract class UserLisaException(var errorMessage: String)(using line: sourcecode.Line, file: sourcecode.File) extends LisaException(errorMessage) {
  def fixTrace(): Unit = ()
}
object UserLisaException {
  class UnapplicableProofTactic(val tactic: ProofTactic, proof: Library#Proof, errorMessage: String)(using sourcecode.Line, sourcecode.File) extends UserLisaException(errorMessage) {
    override def fixTrace(): Unit = {
      val start = getStackTrace.indexWhere(elem => {
        !elem.getClassName.contains(tactic.name)
      }) + 1
      setStackTrace(getStackTrace.take(start))
    }

    val showError: String = {
      val source = scala.io.Source.fromFile(file.value)
      val textline = source.getLines().drop(line.value - 1).next().dropWhile(c => c.isWhitespace)
      source.close()
      Console.RED + proof.owningTheorem.repr + Console.RESET + "\n" +
        ProofPrinter.prettyProof(proof, 2) + "\n" +
        "  " * (1 + proof.depth) + Console.RED + textline + Console.RESET + "\n\n" +
        s"   Proof tactic ${tactic.name} used in.(${file.value.split("/").last.split("\\\\").last}:${line.value}) did not succeed:\n" +
        "   " + errorMessage
    }
  }
  class UnimplementedProof(val theorem: Library#THM)(using sourcecode.Line, sourcecode.File) extends UserLisaException("Unimplemented Theorem") {
    def showError: String = s"Theorem ${theorem.name}"
  }
  class UserParsingException(val parsedString: String, errorMessage: String)(using line: sourcecode.Line, file: sourcecode.File) extends UserLisaException(errorMessage) {
    def showError: String = ""
  }
  class UserInvalidDefinitionException(val symbol: String, errorMessage: String)(using line: sourcecode.Line, file: sourcecode.File) extends UserLisaException(errorMessage) { // TODO refine
    val showError: String = {
      val source = scala.io.Source.fromFile(file.value)
      val textline = source.getLines().drop(line.value - 1).next().dropWhile(c => c.isWhitespace)
      source.close()
      s"   Definition of $symbol at.(${file.value.split("/").last.split("\\\\").last}:${line.value}) is invalid:\n" +
        "   " + Console.RED + textline + Console.RESET + "\n\n" +
        "   " + errorMessage
    }
  }
}
