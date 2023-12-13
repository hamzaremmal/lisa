package lisa.ol

import lisa.fol.FOL.{*, given}
import lisa.kernel.proof.RunningTheory

/**
 * ???
 * @author Hamza REMMAL (hamza.remmal@epfl.ch)
 */
trait OrthologicLibrary extends lisa.prooflib.Library with OLProofHelpers {

  final val theory: RunningTheory = new RunningTheory()

  // ==============================================================================================
  // ================================ SIGNATURE OF ORTHOLATTICES ==================================
  // ==============================================================================================

  final val leq = ConstantPredicateLabel("<=", 2); addSymbol(leq)
  final val eqq = ConstantPredicateLabel("===", 2); addSymbol(eqq)
  final val join = ConstantFunctionLabel("u", 2); addSymbol(join)
  final val meet = ConstantFunctionLabel("n", 2); addSymbol(meet)
  final val neg = ConstantFunctionLabel("!", 1); addSymbol(neg)

  private final val zero = Constant("0"); addSymbol(zero)
  private final val one = Constant("1"); addSymbol(one)

  // ==============================================================================================
  // ========================================= DSL ================================================
  // ==============================================================================================

  extension (left: Term) {
    infix inline def <=(right: Term): Formula = leq(left, right)
    infix inline def ===(right: Term): Formula = eqq(left, right)
    infix inline def u(right: Term): Term = join(left, right)
    infix inline def n(right: Term): Term = meet(left, right)
    inline def unary_! : Term = neg(left)
  }

  given zero2term: Conversion[0, Term] with
    def apply(x: 0): Term = zero

  given one2term: Conversion[1, Term] with
    def apply(x: 1): Term = one

  // ==============================================================================================
  // =============================== AXIMATISATION OF ORTHOLOGIC ==================================
  // ==============================================================================================

  private val (x, y, z) = (Variable("x"), Variable("y"), Variable("z"))

  // See 'Orthologic with Axioms' by S. GUILLOUD and V. KUNCAK
  val P1 = Axiom(x <= y);
  val P2 = Axiom((x <= y) /\ (y <= z) ==> (x <= z))
  val P3 = Axiom(zero <= x)
  val P_3 = Axiom(x <= one)
  val P4 = Axiom((x n y) <= x)
  val P_4 = Axiom(x <= (x u y))
  val P5 = Axiom((x n y) <= y)
  val P_5 = Axiom(y <= (x u y))
  val P6 = Axiom(((x <= y) /\ (x <= z)) ==> (x <= (y n z)))
  val P_6 = Axiom(((x <= y) /\ (x <= z)) ==> ((x u y) <= z))
  val P7 = Axiom(x <= !(!x))
  val P_7 = Axiom(!(!x) <= x)
  val P8 = Axiom((x <= y) ==> (!y <= !x))
  val P9 = Axiom((x n !x) <= zero);
  // val P_9 = Axiom(one <= (x n !x))

  val antisymmetry = Axiom((x <= y) /\ (y <= x) <=> (x === y))
  val lub = Axiom(((x <= z) /\ (y <= z)) <=> ((x u y) <= z))
  val glb = Axiom(((z <= x) /\ (z <= y)) <=> (z <= (x n y)))

  // TODO HR : Define special formula called labelled formula

  // TODO HR : Define sequent from <= operator
  // TODO Question : Does the |- has a meaning in that context or can we replace it with the <= operator ?

}
