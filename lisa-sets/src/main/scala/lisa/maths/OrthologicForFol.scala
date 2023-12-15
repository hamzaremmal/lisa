package lisa.maths

import lisa.fol.FOL as F
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic

object OrthologicForFol extends lisa.Main:

  val x, y, z = variable

//  val weaken = Theorem()

  object RestateWithAxioms extends ProofTactic:

//    trait AnnotatedFormula

    enum AnnotatedFormula:
      case L(f: Formula)
      case R(f: Formula)
      case NoFormula
    import AnnotatedFormula.*

    type SomeAnnotatedFormula = L | R

    
    if true
      then 1
      else 0

    type Sequent2 = (AnnotatedFormula, AnnotatedFormula)

    def apply(using lib: library.type, proof: lib.Proof)
             (axioms: Set[?])
             (bot: F.Sequent): proof.ProofTacticJudgement =

      val botK = bot.underlying
      val (left: Term, right: Term) = ???

      def solve(left: Formula*)(right: Formula*) = (left, right) match

        case (Seq(f1), Seq(f2)) if f1 == f2 =>
          have(left |- right) by Hypothesis

//        case (Seq(f1), Seq(f2)) if ??? => ??? // TODO axioms

//        case (Seq(f1), Seq(f2)) => ??? // weaken

        case (Seq(Neg(f1)), Seq(f2)) =>
          ???

        case (Seq(f1), Seq(f2)) => ???


      def solve2(a1: AnnotatedFormula, a2: AnnotatedFormula) =

//        def solveUsingWeakening(a1: AnnotatedFormula, a2: AnnotatedFormula) =
//          (a1, a2) match
//            case (a1: L | R, a2: L | R) => LazyList(
//                ((a1, NoFormula), step => have()
//                )
//              )


        (a1, a2) match

          case (L(f1), R(f2)) if f1 == f2 => ???
          case (R(f1), L(f2)) if f1 == f2 => ???

      ???

  end RestateWithAxioms

end OrthologicForFol
