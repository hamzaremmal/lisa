package lisa.maths

import collection.mutable.Map as mMap
import lisa.fol.FOL as F
import lisa.prooflib.Library
import lisa.prooflib.ProofTacticLib.ProofTactic

object OrthologicWithAxiomsI extends lisa.Main:

  // ortholattice elements
  val x, y, z = variable


  /** ORTHOLATTICE SYMBOLS */

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


  /** ORTHOLATTICE AXIOMS */

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


  /** ORTHOLOGIC SEQUENT ENCODING */

  val L = ConstantFunctionLabel("L", 1) // Annotate a term as a left formula
  val R = ConstantFunctionLabel("R", 1)

  val S2 = ConstantPredicateLabel("S2", 2)
  val S1 = ConstantPredicateLabel("S1", 1)
  val S0 = ConstantPredicateLabel("S0", 0) // AR shorthand

  Set(L, R, S2, S1, S0) foreach addSymbol


  // IMPROVE with |~ syntax
  def S(t1: Term, t2: Term) = S2(t1, t2)
  def S(t: Term) = S1(t)
  def S() = AppliedPredicate(S0, Seq()) // AR

  extension(left: Term)
    def |~(right: Term) = S(L(left), R(right))

  // annotated formulas
  val f1, f2, f3 = variable

  val i0 = Axiom(S(f1, f2) <=> S(f2, f1))
  val i1 = Axiom(S(L(x), R(y)) <=> (x <= y))
  val i2 = Axiom(S(L(x), L(y)) <=> (x <= not(y)))
  val i3 = Axiom(S(R(x), R(y)) <=> (not(x) <= y))
  val i4 = Axiom(S(L(x)) <=> (x <= zero))
  val i5 = Axiom(S(R(x)) <=> (one <= x))
  val i6 = Axiom(S() <=> (one <= zero))


  /** DERIVATION RULES */

  val hyp = Theorem(x |~ x) {
    have(thesis) by Tautology.from(p1, i1 of (y := x))
  }

  val cut = Theorem(())





  /** RULES */

  val gamma, delta = formulaVariable


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
      ???
    end withParameters

  end RestateWithAxioms

end OrthologicWithAxiomsI
