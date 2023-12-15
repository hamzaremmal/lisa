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

  val leftAnd1 = Theorem((x <= z) ==> ((x n y) <= z)) {
    have(thesis) by Tautology.from(
      p4a,
      p2 of (x := (x n y), y := x)
    )
  }

  val leftAnd2a = Theorem((x <= (not(z))) ==> ((x n y) <= not(z))) { sorry }

  val leftOr1 = Theorem((x <= z) /\ (y <= z) ==> ((x u y) <= z)):
    have(thesis) by Restate.from(p6b)


  val notEquiv = Theorem((x <= not(y)) <=> (y <= not(x))) {
    val dir1 = have((x <= not(y)) ==> (y <= not(x))) subproof {
      have(thesis) by Tautology.from(
        p8 of (y := not(y)), // (x <= not(y)) ==> (not(not(y)) <= not(x))
        p7a of (x := y), // y <= not(not(y))
        p2 of (x := y, y := not(not(y)), z := not(x))
      )
    }
    have(thesis) by Tautology.from(dir1, dir1 of (x := y, y := x))
  }

  val p8Cons = Theorem((not(y) <= not(x)) ==> (x <= y)) {
    have(thesis) by Tautology.from(
      p8 of (x := not(y), y := not(x)), // not(not(x)) <= not(not(y))
      p7a, // x <= not(not(x))
      p7b of (x := y), // not(not(y)) <= y
      p2 of (y := not(not(x)), z := not(not(y))),
      p2 of (y := not(not(y)), z := y),
    )
  }


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
        case NoFormula
      import AnnotatedFormula.*
      type SomeFormula = L | R


      case class Done(conlusion: Any)
      case class Opt1(prem: (AnnotatedFormula, AnnotatedFormula), proofFromPrem: proof.ProofStep => Any)
      case class Opt2(prem1: (AnnotatedFormula, AnnotatedFormula), prem2: (AnnotatedFormula, AnnotatedFormula), proofFromPrem: (proof.ProofStep, proof.ProofStep) => Any)
      type Opt = Done | Opt1 | Opt2


      def solveA(gamma: AnnotatedFormula, delta: AnnotatedFormula): proof.ProofTacticJudgement = TacticSubproof:

        (gamma, delta) match

          // Weaken
//          case (gamma: SomeFormula, delta: SomeFormula) => Seq(
//            Opt1(prem = (gamma, NoFormula), proofFromPrem = s =>
//              have(left <= right) by Tautology.from(
//                s, // left <= 0
//                p3a of (x := right), // 0 <= right
//                p2 of (x := left, y := zero, z := right)
//              )
//            ),
//            Opt1(prem = (NoFormula, R(right)), proofFromPrem = s =>
//              have(left <= right) by Tautology.from(
//                s, // 1 <= right
//                p3b of (x := left), // left <= 1
//                p2 of(x := left, y := one, z := right)
//              )
//            )
//          )

          /****** L R ******/

          case (L(left), R(right)) => (left, right) match

            case (left, right) if left == right => Seq(
              Done(have(left <= right) by Restate.from(p1 of (x := left)))
            )

            case (left, right) => Seq(
              Opt1(prem = (L(left), NoFormula), proofFromPrem = s =>
                have(left <= right) by Tautology.from(
                  s, // left <= 0
                  p3a of (x := right), // 0 <= right
                  p2 of (x := left, y := zero, z := right)
                )
              ),
              Opt1(prem = (NoFormula, R(right)), proofFromPrem = s =>
                have(left <= right) by Tautology.from(
                  s, // 1 <= right
                  p3b of (x := left), // left <= 1
                  p2 of(x := left, y := one, z := right)
                )
              )
            )

            case (not(left), right) => Seq(
              Opt1(prem = (R(left), R(right)), proofFromPrem = s =>
                have(not(left) <= right) by Restate.from(s)
              )
            )

            case (n(l1, l2), right) => Seq(
              Opt1(prem = (L(l1), R(right)), proofFromPrem = s =>
                have((l1 n l2) <= right) by Tautology.from(
                  s, // l1 <= right
                  p4a of (x := l1, y := l2), // (l1 n l2) <= l1
                  p2 of (x := (l1 n l2), y := l1, z := right)
                )
              ),
              Opt1(prem = (L(l2), R(right)), proofFromPrem = s =>
                have((l1 n l2) <= right) by Tautology.from(
                  s, // l2 <= right
                  p5a of (x := l1, y := l2), // (l1 n l2) <= l2
                  p2 of (x := (l1 n l2), y := l2, z := right)
                )
              )
            )

            case (u(l1, l2), right) => Seq(
              Opt2(prem1 = (L(l1), R(right)), prem2 = (L(l2), R(right)), proofFromPrem = (s1, s2) =>
                have((l1 u l2) <= right) by Tautology.from(
                  s1, // l1 <= right
                  s2, // l2 <= right
                  p6b of(x := l1, y := l2, z := right)
                )
              )
            )

            case (left, not(right)) => Seq(
              Opt1(prem = (L(left), L(right)), proofFromPrem = s =>
                have(left <= not(right)) by Restate.from(s)
              )
            )

            case (left, n(r1, r2)) => Seq(
              Opt2(prem1 = (L(left), R(r1)), prem2 = (L(left), R(r2)), proofFromPrem = (s1, s2) =>
                have(left <= (r1 n r2)) by Tautology.from(
                  s1, // left <= r1
                  s2, // left <= r2
                  p6a of(x := left, y := r1, z := r2)
                )
              )
            )

            case (left, u(r1, r2)) => Seq(
              Opt1(prem = (L(left), R(r1)), proofFromPrem = s =>
                have(left <= (r1 n r2)) by Tautology.from(
                  s, // left <= r1
                  p4b of(x := r1, y := r2), // r1 <= (r1 u r2)
                  p2 of(x := left, y := r1, z := (r1 u r2))
                )
              ),
              Opt1(prem = (L(left), R(r2)), proofFromPrem = s =>
                have(left <= (r1 n r2)) by Tautology.from(
                  s, // left <= r2
                  p5b of(x := r1, y := r2), // r2 <= (r1 u r2)
                  p2 of(x := left, y := r2, z := (r1 u r2))
                )
              ),
            )

          /****** L(left1), L(left2) --> left1 <= not(left2) ******/

          case (L(left1), L(left2)) => (left1, left2) match

            case (left1, left2) => Seq(
              Opt1(prem = (L(left1), NoFormula), proofFromPrem = s =>
                have(left1 <= not(left2)) by Tautology.from(
                  s, // left1 <= 0
                  p3a of (x := not(left2)), // 0 <= not(left2)
                  p2 of (x := left1, y := zero, z := not(left2))
                )
              ),
              Opt1(prem = (L(left2), NoFormula), proofFromPrem = s =>
                val s2 = have(left2 <= not(left1)) by Tautology.from(
                  s, // left2 <= 0
                  p3a of (x := not(left1)), // 0 <= not(left1)
                  p2 of (x := left2, y := zero, z := not(left1))
                )
                have(left1 <= not(left2)) by Tautology.from(
                  s2, //
                  notEquiv of (x := left1, y := left2)
                )
              ),
            )

            case (not(left1), left2) => Seq(
              Opt1(prem = (R(left1), L(left2)), proofFromPrem = s =>
                have(not(left1) <= not(left2)) by Tautology.from(
                  s, // left2 <= left1
                  p8Cons of (x := left2, y := left1)
                )
              )
            )

            // AR was same as L R
            case (n(l1, l2), left2) => Seq(
              Opt1(prem = (L(l1), L(left2)), proofFromPrem = s =>
                have((l1 n l2) <= not(left2)) by Tautology.from(
                  s, // l1 <= not(left2)
                  p4a of (x := l1, y := l2), // (l1 n l2) <= l1
                  p2 of (x := (l1 n l2), y := l1, z := not(left2))
                )
              ),
              Opt1(prem = (L(l2), L(left2)), proofFromPrem = s =>
                have((l1 n l2) <= not(left2)) by Tautology.from(
                  s, // l2 <= not(left2)
                  p5a of (x := l1, y := l2), // (l1 n l2) <= l2
                  p2 of (x := (l1 n l2), y := l2, z := not(left2))
                )
              )
            )

            // AR was same as L R
            case (u(l1, l2), left2) => Seq(
              Opt2(prem1 = (L(l1), L(left2)), prem2 = (L(l2), L(left2)), proofFromPrem = (s1, s2) =>
                have((l1 u l2) <= not(left2)) by Tautology.from(
                  s1, // l1 <= not(left2)
                  s2, // l2 <= not(left2)
                  p6b of(x := l1, y := l2, z := not(left2))
                )
              )
            )

            case (left1, not(left2)) => Seq(
              Opt1(prem = (L(left1), R(left2)), proofFromPrem = s =>
                have(left1 <= not(not(left2))) by Tautology.from(
                  s, // left1 <= left2
                  p7a of (x := left2), // left2 <= not(not(left2))
                  p2 of (x := left1, y := left2, z := not(not(left2)))
                )
              )
            )

            case (left1, n(l1, l2)) => Seq(
              Opt2(prem1 = (L(left1), R(l1)), prem2 = (L(left1), R(l2)), proofFromPrem = (s1, s2) =>
                have(left1 <= (l1 n l2)) by Tautology.from(
                  s1, // left <= r1
                  s2, // left <= r2
                  p6a of(x := left1, y := l1, z := l2)
                )
              )
            )

            case (left, u(r1, r2)) => Seq(
              Opt1(prem = (L(left), R(r1)), proofFromPrem = s =>
                have(left <= (r1 n r2)) by Tautology.from(
                  s, // left <= r1
                  p4b of(x := r1, y := r2), // r1 <= (r1 u r2)
                  p2 of(x := left, y := r1, z := (r1 u r2))
                )
              ),
              Opt1(prem = (L(left), R(r2)), proofFromPrem = s =>
                have(left <= (r1 n r2)) by Tautology.from(
                  s, // left <= r2
                  p5b of(x := r1, y := r2), // r2 <= (r1 u r2)
                  p2 of(x := left, y := r2, z := (r1 u r2))
                )
              ),
            )


//          case (L(left1), L(left2)) => (left1, left2)


        ???
      end solveA

      ???
    end withParameters

  end RestateWithAxioms

end OrthologicWithAxioms
