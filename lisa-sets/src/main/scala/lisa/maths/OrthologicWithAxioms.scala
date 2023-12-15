package lisa.maths

import collection.mutable.Map as mMap
import lisa.fol.FOL as F
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic

object OrthologicWithAxioms extends lisa.Main:

  val x, y, z = variable

  /** ORTHOLOGIC SYMBOLS */

  val <= = ConstantPredicateLabel("<=", 2)

  val u = ConstantFunctionLabel("u", 2)
  val n = ConstantFunctionLabel("n", 2)
  val not = ConstantFunctionLabel("¬", 1)

  val zero = Constant("0")
  val one = Constant("1")

  Set(<=, u, n, not, zero, one) foreach addSymbol

  extension (left: Term) // FIX
//    def <=(right: Term): Formula = OrthologicWithAxioms.<=(left, right)
//    def u(right: Term): Term = OrthologicWithAxioms.u(left, right)
//    def n(right: Term): Term = OrthologicWithAxioms.n(left, right)
    def <=(right: Term): Formula = AppliedPredicate(OrthologicWithAxioms.<=, Seq(left, right))
    def u(right: Term): Term = AppliedFunction(OrthologicWithAxioms.u, Seq(left, right))
    def n(right: Term): Term = AppliedFunction(OrthologicWithAxioms.n, Seq(left, right))

  def not(right: Term): Term = AppliedFunction(OrthologicWithAxioms.not, Seq(right))


  val T2F = ConstantPredicateLabel("F", 1)
  addSymbol(T2F)
  val interpretation = Axiom((T2F(x) ==> T2F(y)) <=> (x <= y))


  /** AXIOMS */

  val p1 = Axiom(x <= x)
  val p2 = Axiom((x <= y) /\ (y <= z) ==> (x <= z))
  val p3a = Axiom(zero <= x)
  val p3b = Axiom(x <= one)
  val p4a = Axiom((x n y) <= x)
  val p4b = Axiom(x <= (x u y))
  val p5a = Axiom((x n y) <= y)
  val p5b = Axiom(y <= (x u y))
  val p6a = Axiom((x <= y) /\ (x <= z) ==> (x <= (y n z)))
  val p6b = Axiom((x <= z) /\ (y <= z) ==> ((x u y) <= z))
  val p7a = Axiom(x <= not(not(x)))
  val p7b = Axiom(not(not(x)) <= x)
  val p8 = Axiom((x <= y) ==> (not(y) <= not(x)))
  val p9a = Axiom((x n not(x)) <= zero)
  val p9b = Axiom(one <= (x u not(x)))


  /** RULES */

  val gamma, delta = formulaVariable


  val hyp = Theorem(T2F(x) ==> T2F(x)) {
    have(thesis) by Tautology.from(
      p1,
      interpretation of (y := x)
    )
  }

  val weaken = Theorem(gamma ==> gamma \/ delta)

  val leftAnd = Theorem(gamma /\ !T2F(x) ==> gamma /\ !(T2F(x n y))) {
    have(thesis) by Tautology.from(
      p4a,
      interpretation of (x := (x n y), y := x)
    )
  }

//  val leftOr =

  val leftAnd1 = Theorem((x <= z) ==> ((x n y) <= z)) {
    have(thesis) by Tautology.from(
      p4a,
      p2 of (x := (x n y), y := x)
    )
  }

  val leftAnd2a = Theorem((x <= (not(z))) ==> ((x n y) <= not(z))) { sorry }

  val leftOr1 = Theorem((x <= z) /\ (y <= z) ==> ((x u y) <= z)):
    have(thesis) by Restate.from(p6b)

//  val leftNot1 = Theorem((x <= y) ==> ())


  object RestateWithAxioms extends ProofTactic:

    def apply(using lib: library.type, proof: lib.Proof)
             (axioms: Set[?])
             (bot: F.Sequent): proof.ProofTacticJudgement = ???

    /**
     * Produce proof of () |- left <= right
     */
    def withParameters(using lib: library.type, proof: lib.Proof)
                      (axioms: Set[?])
                      (left: Term, right: Term): proof.ProofTacticJudgement =
      import proof.*

      // TODO RN to Term ?
      enum AnnotatedFormula:
        case L(f: Term)
        case R(f: Term)
        case NoAnnotatedFormula
      import AnnotatedFormula.*
      type SomeAnnotatedFormula = L | R


      case class Done(conlusion: proof.ProofTacticJudgement)
      case class Opt1(prem: (Term, Term), proofFromPrem: proof.ProofStep => proof.ProofTacticJudgement)
      case class Opt2(prem: (Term, Term), proofFromPrem: proof.ProofStep => proof.ProofTacticJudgement)
      type Opt = Done | Opt1 | Opt2

      /*
      case class OlSequent(f1: AnnotatedFormula, f2: AnnotatedFormula):
        def underlying: Sequent =
          val left = Seq(f1, f2) collect { case L(f) => f }
          ???
      */

//      extension (j: proof.ProofTacticJudgement)
//        def map(f: proof.ProofStep => proof.ProofStep): proof.ProofTacticJudgement =
//          j.validate
//          j match
//            case
//          ???

      /* () |- left <= right */
      def solveLR(left: Term, right: Term): proof.ProofTacticJudgement = TacticSubproof:


        val opts = (left, right) match

          case (l, r) if l == r =>
            Seq(
              () => have(l <= r) by Restate.from(p1 of (x := l))
            )

          case (left, right) =>
            def op1 =
              val s1 = solveL(left)
              if !s1.isValid then s1
              else
                have(left <= right) by Tautology.from(
                  have(s1),
                  p3a of (x := right),
                  p2 of (x := left, y := zero, z := right)
                )


            def opt2 = ???

            Seq(op1, opt2)

        ???
      end solveLR

      def solveLL(left: Term, right: Term): proof.ProofTacticJudgement = ???
      def solveRR(left: Term, right: Term): proof.ProofTacticJudgement = ???

      /* () |- left <= 0 */
      def solveL(left: Term): proof.ProofTacticJudgement = ???
      def solveR(right: Term): proof.ProofTacticJudgement = ???




//       TODO
//      val proven, visited: Set[(AnnotatedFormula, AnnotatedFormula)] = mMap.empty

      def solve(left: Term, right: Term): proof.ProofTacticJudgement =

//        val opts: Seq[proof.ProofTacticJudgement | Opt] = (left, right) match
        val opts = (left, right) match

          case (l, r) if l == r =>
            have(l <= r) by Restate.from(p1 of (x := l))

//          case (l, r) if axioms // TODO

          case (not(l), r) => ???

          case (n(a, b), r) => Seq(
//            Opt(prems = (a, r), proofFromPrem = (s: proof.ProofStep) =>
//              have(left <= right) by Tautology.from(
//                p4a of (x := a, y := b), // (a n b) <= a
//                s, // a <= r
//                p2 of (x := (a n b), y := a, z := r)
//              )
//            ),
//            Opt(prems = (b, r), proofFromPrem = (s: proof.ProofStep) =>
//              have(left <= right) by Tautology.from(
//                p5a of (x := a, y := b), // (a n b) <= b
//                s, // b <= r
//                p2 of (x := (a n b), y := b, z := r)
//              )
//            )
          )

          case (u(a, b), r) =>

            ???


        ???
      end solve

      def solveA(left: AnnotatedFormula, right: AnnotatedFormula): proof.ProofTacticJudgement =

        // TODO assuming ordered by L, R, None
        val goal: Formula = (left, right) match
          case (L(f1), R(f2)) => f1 <= f2
          case (L(f1), L(f2)) => f1 <= not(f2)
          case (R(f1), R(f2)) => not(f1) <= f2
          case (L(f1), None) => f1 <= zero
          case (R(f1), None) => one <= f1

        val opts: Seq[Opt] = ???

        def solveWithHyp = (left, right) match
          case (L(f1), R(f2)) if f1 == f2 =>
            Done(have(f1 <= f2) by Tautology.from(p1))
          case (R(f1), L(f2)) if f1 == f2 =>
            Done(have(f2 <= f1) by Tautology.from(p1))

        def solveWithWeaken = (left, right) match
          case (left: SomeAnnotatedFormula, right: SomeAnnotatedFormula) =>

            Opt1(
              prem = (left, NoAnnotatedFormula),
              proofFromPrem = (s: proof.ProofStep) =>
                have(goal) by Tautology.from(
                  ???
                )
            )

            ???

        def solveWithLeftNot = (left, right) match

          case (L(not(f1)), r) =>
            val prem = (R(f1), r)
            val proofFromPrem =


            ???

        ???
      end solveA

      ???
    end withParameters

  end RestateWithAxioms

end OrthologicWithAxioms
